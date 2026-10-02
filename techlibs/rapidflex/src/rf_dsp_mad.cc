#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "rf_dsp_mad_pm.h"

static void create_rf_mad_dsp(rf_dsp_mad_pm &pm) {
  auto &st = pm.st_rf_dsp_mad;

  // Reject if multiplier drives anything else than $add
  if (st.mul_nusers > 2) {
    return;
  }

  // Get port widths
  size_t a_width = GetSize(st.mul->getPort(ID(A)));
  size_t b_width = GetSize(st.mul->getPort(ID(B)));
  size_t c_width = GetSize(st.add->getPort(ID(A)));
  if (st.add_ba == ID(B)) {
    c_width = GetSize(st.add->getPort(ID(B)));
  }
  size_t z_width = GetSize(st.add->getPort(ID(Y)));

  size_t min_width = std::min(a_width, b_width);
  size_t max_width = std::max(a_width, b_width);

  // Signed / unsigned
  bool a_signed = st.mul->getParam(ID(A_SIGNED)).as_bool();
  bool b_signed = st.mul->getParam(ID(B_SIGNED)).as_bool();
  bool c_signed = st.add->getParam(ID(A_SIGNED)).as_bool();
  if (st.add_ba == ID(B)) {
    c_signed = st.add->getParam(ID(B_SIGNED)).as_bool();
  }

  // Determine DSP type or discard if too narrow / wide
  RTLIL::IdString type;
  size_t tgt_a_width;
  size_t tgt_b_width;
  size_t tgt_c_width;
  size_t tgt_z_width;

  string cell_base_name = "mad";
  string cell_size_name = "";
  string cell_cfg_name = "";
  string cell_full_name = "";

  if (min_width <= 2 && max_width <= 2 && z_width <= 4) {
    // Too narrow
    return;
  } else if (min_width <= 12 && max_width <= 10 && z_width <= 22) {
    cell_size_name = "12x10x22";
    tgt_a_width = 12;
    tgt_b_width = 10;
    tgt_c_width = 22;
    tgt_z_width = 22;
  } else if (min_width <= 24 && max_width <= 20 && z_width <= 44) {
    cell_size_name = "24x20x44";
    tgt_a_width = 24;
    tgt_b_width = 20;
    tgt_c_width = 44;
    tgt_z_width = 44;
  } else {
    // Too wide
    return;
  }

  cell_full_name = cell_base_name + cell_size_name + cell_cfg_name;

  type = RTLIL::escape_id(cell_full_name);
  log("Inferring MAD %zux%zu+%zu->%zu as %s from:\n", a_width, b_width, c_width,
      z_width, RTLIL::unescape_id(type).c_str());

  for (auto cell : {st.mul, st.add}) {
    if (cell != nullptr) {
      log(" %s (%s)\n", RTLIL::unescape_id(cell->name).c_str(),
          RTLIL::unescape_id(cell->type).c_str());
    }
  }

  // Build the DSP cell name
  std::string name;
  name += RTLIL::unescape_id(st.mul->name) + "_";
  name += RTLIL::unescape_id(st.add->name) + "_";

  // Add the DSP cell
  RTLIL::Cell *cell = pm.module->addCell(RTLIL::escape_id(name), type);

  // Set attributes
  cell->set_bool_attribute(RTLIL::escape_id("is_inferred"), true);

  // Get input/output data signals
  RTLIL::SigSpec sig_a;
  RTLIL::SigSpec sig_b;
  RTLIL::SigSpec sig_c;
  RTLIL::SigSpec sig_z;

  if (a_width >= b_width) {
    sig_a = st.mul->getPort(ID(A));
    sig_b = st.mul->getPort(ID(B));
  } else {
    sig_a = st.mul->getPort(ID(B));
    sig_b = st.mul->getPort(ID(A));
  }

  sig_c = st.add->getPort(ID(A));
  if (st.add_ba == ID(B)) {
    sig_c = st.add->getPort(ID(B));
  }
  sig_z = st.add->getPort(ID(Y));

  // Connect input data ports, sign extend / pad with zeros
  sig_a.extend_u0(tgt_a_width, a_signed);
  sig_b.extend_u0(tgt_b_width, b_signed);
  sig_c.extend_u0(tgt_c_width, c_signed);
  cell->setPort(RTLIL::escape_id("A0"), sig_a);
  cell->setPort(RTLIL::escape_id("B0"), sig_b);

  // Connect input data port, pad if needed
  if ((size_t)GetSize(sig_c) < tgt_c_width) {
    auto *wire = pm.module->addWire(NEW_ID, tgt_c_width - GetSize(sig_c));
    sig_c.append(wire);
  }
  cell->setPort(RTLIL::escape_id("C0"), sig_c);

  // Connect output data port, pad if needed
  if ((size_t)GetSize(sig_z) < tgt_z_width) {
    auto *wire = pm.module->addWire(NEW_ID, tgt_z_width - GetSize(sig_z));
    sig_z.append(wire);
  }
  cell->setPort(RTLIL::escape_id("Y"), sig_z);

  bool subtract = (st.add->type == RTLIL::escape_id("$sub"));
  if (subtract) {
    cell->setPort(RTLIL::escape_id("subtract_i"),
                  RTLIL::SigSpec(subtract ? RTLIL::S1 : RTLIL::S0));
  }

  // Mark the cells for removal
  pm.autoremove(st.mul);
  pm.autoremove(st.add);
}

struct RfDspMacc : public Pass {
  // Local variables
  bool show_help;

  RfDspMacc()
      : Pass("rf_dsp_mad", "Extract multiply-add and multiply-subtract "
                           "operators and map to dedicated DSPs") {}

  void help() override {
    log("\n");
    log("    rf_dsp_mad [options] [selection]\n");
    log("\n");
    log("    Extract multiply-add and multiply-subtract operators and map to "
        "dedicated DSPs\n");
    log("\n");
    log("    -help: show help desk\n");
    log("\n");
  }

  void clear_flags() override { show_help = false; }

  void execute(std::vector<std::string> a_Args,
               RTLIL::Design *a_Design) override {
    log_header(a_Design, "Executing RF_DSP_MAD pass.\n");

    size_t argidx;
    for (argidx = 1; argidx < a_Args.size(); argidx++) {
      if (a_Args[argidx] == "-help") {
        show_help = true;
        continue;
      }
      break;
    }
    extra_args(a_Args, argidx, a_Design);
    if (show_help) {
      help();
      return;
    }

    for (auto module : a_Design->selected_modules()) {
      rf_dsp_mad_pm(module, module->selected_cells())
          .run_rf_dsp_mad(create_rf_mad_dsp);
    }
  }

} RfDspMad;

PRIVATE_NAMESPACE_END
