#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "rf_new_dsp_pm.h"

void swapinput(RTLIL::SigSpec &sigA, RTLIL::SigSpec &sigB) {
  if (GetSize(sigA) < GetSize(sigB)) {
    RTLIL::SigSpec sigC = sigB;
    sigB = sigA;
    sigA = sigC;
  }
}

void rf_new_dsp(rf_new_dsp_pm &pm) {
  auto &st = pm.st_rf_new_dsp;

  log("mul1: %s\n", log_id(st.mul1, "--"));
  log("mul2: %s\n", log_id(st.mul2, "--"));
  log("mul3: %s\n", log_id(st.mul3, "--"));
  log("mul4: %s\n", log_id(st.mul4, "--"));
  log("postAdd1: %s\n", log_id(st.postAdd1, "--"));
  log("postAdd2: %s\n", log_id(st.postAdd2, "--"));
  log("postAdd3: %s\n", log_id(st.postAdd3, "--"));
  log("postAdd4: %s\n", log_id(st.postAdd4, "--"));

  RTLIL::SigSpec sigA, sigB, sigD, sigY;

  // mode
  string mode;
  if (st.level == 4) {
    if (st.dinput)
      mode +=
          "1001"; // 4-level mac with d input: d + a1*b1 + a2*b2 + a3*b3 + a4*b4
    else
      mode +=
          "0000"; // 4-level mac without d input: a1*b1 + a2*b2 + a3*b3 + a4*b4
  }
  if (st.level == 3)
    mode += "1001"; // 3-level mac with d input: d + a1*b1 + a2*b2 + a3*b3
  if (st.level == 2) {
    if (st.dinput)
      mode += "0001"; // 2-level mac with d input: d + a1*b1 + a2*b2
    else
      mode += "0010"; // 2-level mac without d input: a1*b1 + a2*b2
  }
  if (st.level == 1) {
    if (st.dinput)
      mode += "0101"; // 1-level mac with d input: d + a1*b1
    else
      return;
  }

  // input size
  int n_size = 0;
  int m_size = 0;
  int d_size = 0;

  string cell_base_name = "mad";
  string cell_size_name = "";
  string cell_cfg_name = "";
  string cell_full_name = "";

  if (st.mul1) {
    swapinput(st.sigA1, st.sigB1);
    n_size = n_size > GetSize(st.sigA1) ? n_size : GetSize(st.sigA1);
    m_size = m_size > GetSize(st.sigB1) ? m_size : GetSize(st.sigB1);
  }

  if (st.mul2) {
    swapinput(st.sigA2, st.sigB2);
    n_size = n_size > GetSize(st.sigA2) ? n_size : GetSize(st.sigA2);
    m_size = m_size > GetSize(st.sigB2) ? m_size : GetSize(st.sigB2);
  }

  if (st.mul3) {
    swapinput(st.sigA3, st.sigB3);
    n_size = n_size > GetSize(st.sigA3) ? n_size : GetSize(st.sigA3);
    m_size = m_size > GetSize(st.sigB3) ? m_size : GetSize(st.sigB3);
  }

  if (st.mul4) {
    swapinput(st.sigA4, st.sigB4);
    n_size = n_size > GetSize(st.sigA4) ? n_size : GetSize(st.sigA4);
    m_size = m_size > GetSize(st.sigB4) ? m_size : GetSize(st.sigB4);
  }

  if (st.dinput)
    d_size = GetSize(st.sigD);

  if (mode == "0100") {
    n_size = (n_size + 1) / 2;
    m_size = (m_size + 1) / 2;
  }

  if (n_size <= 2 && m_size <= 2 && d_size <= 4) {
    // Too narrow
    return;
  } else if (n_size <= 12 && m_size <= 10 && d_size <= 30) {
    cell_size_name = "12x10x22";
    n_size = 12;
    m_size = 10;
    d_size = 30;
  } else if (n_size <= 24 && m_size <= 20 && d_size <= 52) {
    cell_size_name = "24x20x44";
    n_size = 24;
    m_size = 20;
    d_size = 52;
  } else {
    // Too wide
    return;
  }

  // cell
  cell_full_name = cell_base_name + cell_size_name + cell_cfg_name;

  string cellname;
  cellname += "newdsp_" + RTLIL::unescape_id(st.mul1->name);
  RTLIL::Cell *cell = pm.module->addCell(RTLIL::escape_id(cellname),
                                         RTLIL::escape_id(cell_full_name));

  // D input
  bool d_signed = false;
  if (st.dinput) {
    d_signed = st.postAdd1->getParam(ID(A_SIGNED)).as_bool();
    if (mode == "0001")
      sigD.extend_u0(d_size);
    sigD.append(st.sigD);
  }
  sigD.extend_u0(2 * d_size, d_signed);

  // output
  if (st.multiout2 || st.multiout3) {
    auto *wire = pm.module->addWire(NEW_ID, d_size - GetSize(st.sigY2));
    sigY.append(st.sigY2);
    sigY.append(wire);
    sigY.append(st.sigY);
  } else if (mode == "0001" || (st.level == 4 && st.dinput)) {
    auto *wire = pm.module->addWire(NEW_ID, d_size);
    sigY.append(wire);
    sigY.append(st.sigY);
  } else
    sigY.append(st.sigY);
  auto *wire = pm.module->addWire(NEW_ID, 2 * d_size - GetSize(sigY));
  sigY.append(wire);

  // input
  bool a_signed, b_signed;
  if (mode == "0001") {
    sigA.extend_u0(2 * n_size);
    sigB.extend_u0(2 * m_size);
  }
  if (st.mul1 && mode != "0100") {
    a_signed = st.mul1->getParam(ID(A_SIGNED)).as_bool();
    b_signed = st.mul1->getParam(ID(B_SIGNED)).as_bool();
    st.sigA1.extend_u0(n_size, a_signed);
    st.sigB1.extend_u0(m_size, b_signed);
    sigA.append(st.sigA1);
    sigB.append(st.sigB1);
  }
  if (mode == "0100") {
    a_signed = st.mul1->getParam(ID(A_SIGNED)).as_bool();
    b_signed = st.mul1->getParam(ID(B_SIGNED)).as_bool();
    st.sigA1.extend_u0(2 * n_size, a_signed);
    st.sigB1.extend_u0(2 * m_size, b_signed);
    sigA.append(st.sigA1);
    sigB.append(st.sigB1);
  }
  if (!st.dinput && st.mul4) {
    a_signed = st.mul4->getParam(ID(A_SIGNED)).as_bool();
    b_signed = st.mul4->getParam(ID(B_SIGNED)).as_bool();
    st.sigA4.extend_u0(n_size, a_signed);
    st.sigB4.extend_u0(m_size, b_signed);
    sigA.append(st.sigA4);
    sigB.append(st.sigB4);
  }
  if (st.mul2) {
    a_signed = st.mul2->getParam(ID(A_SIGNED)).as_bool();
    b_signed = st.mul2->getParam(ID(B_SIGNED)).as_bool();
    st.sigA2.extend_u0(n_size, a_signed);
    st.sigB2.extend_u0(m_size, b_signed);
    sigA.append(st.sigA2);
    sigB.append(st.sigB2);
  }
  if (st.mul3) {
    a_signed = st.mul3->getParam(ID(A_SIGNED)).as_bool();
    b_signed = st.mul3->getParam(ID(B_SIGNED)).as_bool();
    st.sigA3.extend_u0(n_size, a_signed);
    st.sigB3.extend_u0(m_size, b_signed);
    sigA.append(st.sigA3);
    sigB.append(st.sigB3);
  }
  if (st.dinput && st.mul4) {
    a_signed = st.mul4->getParam(ID(A_SIGNED)).as_bool();
    b_signed = st.mul4->getParam(ID(B_SIGNED)).as_bool();
    st.sigA4.extend_u0(n_size, a_signed);
    st.sigB4.extend_u0(m_size, b_signed);
    sigA.append(st.sigA4);
    sigB.append(st.sigB4);
  }
  sigA.extend_u0(4 * n_size);
  sigB.extend_u0(4 * m_size);

  // reg
  mode = "00000" + mode + "0000";
  if (st.level == 1) {
    if (st.ffA1 && st.ffB1 && !(st.dinput && !st.ffD)) {
      mode[1] = mode[2] = '1';
      pm.autoremove(st.ffA1);
      pm.autoremove(st.ffB1);
      if (st.dinput)
        pm.autoremove(st.ffD);
    }
    if (st.ffM1 && st.ffD && st.postAdd1) {
      mode[11] = '1';
      pm.autoremove(st.ffM1);
      pm.autoremove(st.ffD);
    }
    if (st.ffY1 || (!st.postAdd1 && st.ffM1)) {
      mode[3] = mode[4] = '1';
      pm.autoremove(st.ffY1);
      pm.autoremove(st.ffM1);
    }
  }
  if (st.level == 2) {
    if (st.ffA1 && st.ffB1 && st.ffA2 && st.ffB2 && st.dinput &&
        st.ffD) // in reg
    {
      mode[1] = mode[2] = '1';
      pm.autoremove(st.ffA1);
      pm.autoremove(st.ffB1);
      pm.autoremove(st.ffA2);
      pm.autoremove(st.ffB2);
      pm.autoremove(st.ffD);
    }
    if (st.ffA1 && st.ffB1 && st.ffA4 && st.ffB4 && !st.dinput) // in reg
    {
      mode[1] = mode[2] = '1';
      pm.autoremove(st.ffA1);
      pm.autoremove(st.ffB1);
      pm.autoremove(st.ffA4);
      pm.autoremove(st.ffB4);
    }
    if (st.ffM1 && ((st.dinput && st.ffM2) || st.ffD)) // mul in reg
    {
      mode[11] = '1';
      pm.autoremove(st.ffM1);
      pm.autoremove(st.ffD);
      if (st.dinput)
        pm.autoremove(st.ffM2);
    }
    if (st.ffY1 && st.ffY2 && st.dinput) // mul out reg
    {
      mode[12] = '1';
      pm.autoremove(st.ffY1);
      pm.autoremove(st.ffY2);
    } else if (st.ffY1 || st.ffY2) // out reg
    {
      mode[3] = mode[4] = '1';
      pm.autoremove(st.ffY1);
      pm.autoremove(st.ffY2);
    }
  }
  if (st.ffA1 && st.ffB1 && st.ffA2 && st.ffB2 && st.dinput &&
      st.ffD) // in reg low
  {
    mode[2] = '1';
    pm.autoremove(st.ffA1);
    pm.autoremove(st.ffB1);
    pm.autoremove(st.ffA2);
    pm.autoremove(st.ffB2);
    pm.autoremove(st.ffD);
  }
  if (st.ffA1 && st.ffB1 && st.ffA4 && st.ffB4 && !st.dinput) // in reg low
  {
    mode[2] = '1';
    pm.autoremove(st.ffA1);
    pm.autoremove(st.ffB1);
    pm.autoremove(st.ffA4);
    pm.autoremove(st.ffB4);
  }
  if (st.level == 3) {
    if (st.ffA3 && st.ffB3 && st.dinput) // in reg high
    {
      mode[1] = '1';
      pm.autoremove(st.ffA3);
      pm.autoremove(st.ffB3);
    }
    if (st.ffA2 && st.ffB2 && !st.dinput) // in reg high
    {
      mode[1] = '1';
      pm.autoremove(st.ffA2);
      pm.autoremove(st.ffB2);
    }
    if (st.ffM1 && st.ffM2 && ((st.dinput && st.ffM3) || st.ffD)) // mul in reg
    {
      mode[11] = '1';
      pm.autoremove(st.ffM1);
      pm.autoremove(st.ffD);
      pm.autoremove(st.ffM2);
      if (st.dinput)
        pm.autoremove(st.ffM3);
    }
    if (st.ffY1 && st.ffY2 && !(st.dinput && !st.ffY3)) // mul out reg
    {
      mode[12] = '1';
      pm.autoremove(st.ffY1);
      pm.autoremove(st.ffY2);
      if (st.dinput)
        pm.autoremove(st.ffY3);
    } else if (st.ffY2 || st.ffY3) // out reg
    {
      mode[3] = mode[4] = '1';
      pm.autoremove(st.ffY2);
      pm.autoremove(st.ffY3);
    }
  }
  if (st.level == 4) {
    if (st.ffA3 && st.ffB3 && st.ffA4 && st.ffB4 && st.dinput) // in reg high
    {
      mode[1] = '1';
      pm.autoremove(st.ffA3);
      pm.autoremove(st.ffB3);
      pm.autoremove(st.ffA4);
      pm.autoremove(st.ffB4);
    }
    if (st.ffA2 && st.ffB2 && st.ffA3 && st.ffB3 && !st.dinput) // in reg high
    {
      mode[1] = '1';
      pm.autoremove(st.ffA2);
      pm.autoremove(st.ffB2);
      pm.autoremove(st.ffA3);
      pm.autoremove(st.ffB3);
    }
    if (st.ffM1 && st.ffM2 && st.ffM3 &&
        ((st.dinput && st.ffM4) || st.ffD)) // mul in reg
    {
      mode[11] = '1';
      pm.autoremove(st.ffM1);
      pm.autoremove(st.ffD);
      pm.autoremove(st.ffM2);
      pm.autoremove(st.ffM3);
      if (st.dinput)
        pm.autoremove(st.ffM4);
    }
    if (st.ffY1 && st.ffY2 && st.ffY3 &&
        !(st.dinput && !st.ffY4)) // mul out reg
    {
      mode[12] = '1';
      pm.autoremove(st.ffY1);
      pm.autoremove(st.ffY2);
      pm.autoremove(st.ffY3);
      if (st.dinput)
        pm.autoremove(st.ffY4);
    } else if (st.ffY3 || st.ffY4) // out reg high
    {
      if (st.multiout2 || st.multiout3)
        mode[3] = '1';
      else
        mode[3] = mode[4] = '1';
      pm.autoremove(st.ffY3);
      pm.autoremove(st.ffY4);
    }
    if (st.ffMY) // out reg low
    {
      mode[4] = '1';
      pm.autoremove(st.ffMY);
    }
  }

  cell->setPort(RTLIL::escape_id("a_i"), sigA);
  cell->setPort(RTLIL::escape_id("b_i"), sigB);
  cell->setPort(RTLIL::escape_id("d_i"), sigD);
  cell->setPort(RTLIL::escape_id("out_o"), sigY);
  cell->setPort(RTLIL::escape_id("mode_i"), Const::from_string(mode));
  if (st.clock != SigBit())
    cell->setPort(RTLIL::escape_id("clk_i"), st.clock);
  cell->setPort(RTLIL::escape_id("rst_acc"), RTLIL::SigSpec(0, 1));
  cell->setPort(RTLIL::escape_id("accsel"), RTLIL::SigSpec(0, 1));
  cell->setPort(RTLIL::escape_id("cas_g"), RTLIL::SigSpec(0, 1));

  pm.autoremove(st.mul1);
  pm.autoremove(st.mul2);
  pm.autoremove(st.mul3);
  pm.autoremove(st.mul4);
  pm.autoremove(st.postAdd1);
  pm.autoremove(st.postAdd2);
  pm.autoremove(st.postAdd3);
  pm.autoremove(st.postAdd4);
}

struct RfNewDSP : public Pass {
  bool show_help;

  RfNewDSP()
      : Pass("rf_new_dsp",
             "Extract multiply-add operators and map to new_dsps") {}

  void help() override {
    log("\n");
    log("    rf_new_dsp [options] [selection]\n");
    log("\n");
    log("    Extract multiply-add operators and map to new_dsps\n");
    log("\n");
    log("    -help: show help desk\n");
    log("\n");
    log("    -n_size: specify input n size\n");
    log("\n");
    log("    -m_size: specify input m size\n");
    log("\n");
  }

  void clear_flags() override { show_help = false; }

  void execute(std::vector<std::string> a_Args,
               RTLIL::Design *a_Design) override {
    log_header(a_Design, "Executing RF_NEW_DSP pass.\n");
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
      rf_new_dsp_pm pm(module, module->selected_cells());
      pm.run_rf_new_dsp(rf_new_dsp);
    }
  }
} RfNewDsp;

PRIVATE_NAMESPACE_END
