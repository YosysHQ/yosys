#include <algorithm>
#include <cstdio>
#include <iostream>
#include <string>

#include "backends/rtlil/rtlil_backend.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include "pugixml.hpp"
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct InsertClockBuffer : public Pass {
  InsertClockBuffer()
      : Pass("insert_clock_buffer",
             "This command is to insert clock buffer into the design") {}

  /*utility function used by insert_ckbuff; copied from blif.cc*/
  const std::string str(RTLIL::IdString id) {
    std::string str = RTLIL::unescape_id(id);
    for (size_t i = 0; i < str.size(); i++)
      if (str[i] == '#' || str[i] == '=' || str[i] == '<' || str[i] == '>')
        str[i] = '?';
    return str;
  }

  /*utility function used by insert_ckbuff; copied from blif.cc*/
  const std::string str(RTLIL::SigBit sig) {
    if (sig.wire == NULL) {
      return "null";
    }

    std::string str = RTLIL::unescape_id(sig.wire->name);
    for (size_t i = 0; i < str.size(); i++)
      if (str[i] == '#' || str[i] == '=' || str[i] == '<' || str[i] == '>')
        str[i] = '?';

    if (sig.wire->width != 1)
      str +=
          stringf("[%d]", sig.wire->upto ? sig.wire->start_offset +
                                               sig.wire->width - sig.offset - 1
                                         : sig.wire->start_offset + sig.offset);

    return str;
  }

  // eval_lut: Evaluate the output of a single LUT based on given input values
  // Parameters:
  //   lut    - Pointer to an RTLIL $lut cell
  //   inputs - map<SigBit, bool> specifying the values of input signals
  //            (can provide only a subset of inputs)
  //   sigmap - SigMap, used to get the actual driving signal for each input
  // Returns:
  //   Boolean output of the LUT (true/false)
  bool eval_lut(const RTLIL::Cell *lut, std::map<SigBit, bool> inputs,
                const SigMap &sigmap) {
    // Get the input vector of the LUT and map each signal to its actual driver
    SigSpec lut_inputs = sigmap(lut->getPort(ID::A));

    // Number of LUT inputs
    int width = lut->getParam(ID::WIDTH).as_int();

    // LUT truth table storing output for each input combination
    Const lut_table = lut->getParam(ID::LUT);

    // Index into the LUT truth table
    int lut_index = 0;

    // Iterate through each input bit
    for (int i = 0; i < width; i++) {
      // Get the i-th input signal and map it to its final driver
      SigBit bit = sigmap(lut_inputs[i]);

      // Boolean value of the current input
      bool value;

      // If the input value is provided by the user, use it
      if (inputs.count(bit))
        value = inputs[bit];
      // Otherwise, use the signal's default or constant value
      else
        value = SigSpec(bit).as_bool();

      // Accumulate this bit into the LUT index
      // '<< i' places the value at the correct bit position
      lut_index |= (value << i);
    }

    // Lookup the LUT output for the computed index and return as bool
    return lut_table.extract(lut_index).as_bool();
  }

  /* This function rewires subckt such as flip-flops (FFs) and pcounter that use
  internally generated signals as their clock inputs. We can perform this
  rewiring before connecting the new clock buffer (ckbuf), because the new wires
  are added to the top module—not to the ckbuf itself. Therefore, once an
  internally generated clock is detected, a new wire is created in the top
  module and directly connected to the affected subckt. This rewiring process is
  independent of the addition of the ckbuf. */
  void rewire_subckt(RTLIL::Module *module, RTLIL::Cell *cell,
                     RTLIL::IdString id_name, std::string C_input) {
    std::string C_output = C_input + "_ckbuf";
//    if (!module->wire("\\" + C_output)) {
//      auto output_wire = module->addWire("\\" + C_output, 1);
//    }
    /* connect new ckbuf to the subckt */
    cell->unsetPort(id_name); // unsetPort("C")
    cell->setPort(id_name, module->wire("\\" + C_output));
    cell->fixup_parameters();
  }

  /* This is a general-purpose function that works for all subcircuits (subckt).
   It detects clock and reset signals and determines whether they are global.
   If any global signal is detected, the function will rewire the subcircuit
   accordingly.
   */
  void process_cell(RTLIL::Module *module, RTLIL::Cell *cell,
                    std::map<int, RTLIL::Wire *> inputs,
                    std::vector<RTLIL::IdString> clk_indicator_group,
                    std::vector<RTLIL::IdString> reset_indicator_group,
                    std::set<std::string> &ckbuf_info,
                    std::map<std::string, std::string> &ckbuf_type) {
    RTLIL::IdString clk_indicator;
    for (auto clk : clk_indicator_group) {
      if (cell->hasPort(clk)) {
        clk_indicator = clk;
        break;
      }
    }

    // dff could have reset signal with keywords R or RN. We shall determine
    // which is the port name for current cell
    RTLIL::IdString reset_indicator;
    for (auto rst : reset_indicator_group) {
      if (cell->hasPort(rst)) {
        reset_indicator = rst;
        break;
      }
    }

    if (reset_indicator.empty() && clk_indicator.empty()) {
      return;
    }

    bool global_clock = false;
    bool global_reset = false;
    for (auto &it : inputs) {
      RTLIL::Wire *wire = it.second;
      for (int i = 0; i < wire->width; i++) {
        if (cell->hasPort(clk_indicator)) {
          if (cell->getPort(clk_indicator) == RTLIL::SigSpec(wire, i)) {
            global_clock = true;
            continue; /*if the signal is global clock, then there is no need
                         to check whether it is global reset or not*/
          }
        }

        if (cell->hasPort(reset_indicator)) {
          if (cell->getPort(reset_indicator) == RTLIL::SigSpec(wire, i)) {
            global_reset = true;
          }
        }
      }
    }
    /*grab the information of the internally generated clocks*/
    if (!global_clock && cell->hasPort(clk_indicator)) {
      std::string C_input = str(cell->getPort(clk_indicator)).c_str();
      ckbuf_info.insert(C_input);
      ckbuf_type[C_input] = "clock";
      rewire_subckt(module, cell, clk_indicator, C_input);
    }
    /*grab the information of the internally generated resets*/
    if (!global_reset && cell->hasPort(reset_indicator)) {
      std::string C_input = str(cell->getPort(reset_indicator)).c_str();
      ckbuf_info.insert(C_input);
      ckbuf_type[C_input] = "reset";
      rewire_subckt(module, cell, reset_indicator, C_input);
    }
  }

  /* This function examines sequential logic and returns a set of strings
  representing internally generated signals. When such a signal is found, it
  invokes rewire_subckt.*/
  std::set<std::string>
  find_internal_clk_r_signal(RTLIL::Module *module,
                             std::map<std::string, std::string> &ckbuf_type) {
    std::set<std::string> ckbuf_info;
    /*get input ports of the top module*/
    std::map<int, RTLIL::Wire *> inputs, outputs;
    for (auto wire : module->wires()) {
      if (wire->port_input)
        inputs[wire->port_id] = wire;
    }
    for (auto cell : module->cells()) {
      /*Bypass yosys internal cells $lut which doesn't have clock signal */
      if ((cell->type) == ID($lut)) {
        continue;
      } else {
        /*check whether the C port is internally generated clock signal or not*/
        std::vector<RTLIL::IdString> clk_indicator_group = {ID(C), ID(clk_i)};
        std::vector<RTLIL::IdString> reset_indicator_group = {ID(RN), ID(R),
                                                              ID(rst_i)};
        process_cell(module, cell, inputs, clk_indicator_group,
                     reset_indicator_group, ckbuf_info, ckbuf_type);
      }
    }
    return ckbuf_info;
  }

  /* insert .subckt ckbuf for each internally generated clock or reset signal */
  void insert_ckbuf(RTLIL::Module *module,
                    const std::set<std::string> &ckbuf_info) {
    for (const std::string &ckbuf : ckbuf_info) {
      RTLIL::Cell *ckbuf_cell =
          module->addCell(stringf("$ckbuf$%s", ckbuf.c_str()), "\\ckbuf");
      ckbuf_cell->setPort("\\in", module->wire("\\" + ckbuf));
      ckbuf_cell->setPort("\\out", module->wire("\\" + ckbuf + "_ckbuf"));
      ckbuf_cell->set_src_attribute("");
    }
  }

  /*This function is for generating cell map file*/
  void generate_cell_map(const char *fname,
                         const std::set<std::string> &ckbuf_info,
                         const std::map<std::string, std::string> &ckbuf_type) {
    pugi::xml_document out_xml;
    pugi::xml_node root_node = out_xml.append_child("ckbuf_cell_map");
    for (const std::string &ckbuf : ckbuf_info) {
      std::string in = ckbuf;
      std::string out = ckbuf + "_ckbuf";
      std::string type;

      auto it = ckbuf_type.find(ckbuf);
      if (it != ckbuf_type.end()) {
        type = it->second;
      } else {
        log_error("No port type defined for ckbuf %s \n", out.c_str());
      }

      pugi::xml_node ckbuf_node = root_node.append_child("ckbuf");
      ckbuf_node.append_attribute("input_net") = in.c_str();
      ckbuf_node.append_attribute("cell") = out.c_str();
      ckbuf_node.append_attribute("type") = type.c_str();
    }
    out_xml.save_file(fname);
    log("cell map is stored in file %s \n", fname);
  }
  void rewire_lut_primitive(RTLIL::Cell *cell,
                            const std::vector<RTLIL::SigBit> &sig,
                            const RTLIL::Const &new_lut, int new_width) {
    cell->unsetPort(ID::A);
    cell->setPort(ID::A, sig);

    //  Update LUT parameters
    cell->parameters[ID::LUT] = new_lut; // Set new truth table
    cell->parameters[ID::WIDTH] = new_width;
    cell->fixup_parameters();
  }

  void process_cell_rewire_lut(
      RTLIL::Module *module, RTLIL::Cell *cell,
      const std::map<std::string, std::set<RTLIL::SigBit>>
          &internal_signal_io_map,
      const std::map<std::string, std::string> &internal_signal_lut,
      const Yosys::SigMap &sigmap) {
    std::set<RTLIL::SigBit> sig;
    /* sig and ordered_sig contain the same signals.
     * sig is used to store the rewired signals and avoid duplicates,
     * while ordered_sig preserves the signal order so it stays aligned
     * with the truth table information.
     */
    std::vector<RTLIL::SigBit> ordered_sig;
    std::map<RTLIL::SigBit, std::set<RTLIL::SigBit>> sig_replace_port_map;
    std::map<RTLIL::SigBit, RTLIL::IdString> sig_replace_cell_map;
    std::set<RTLIL::SigBit> temp_sig;
    std::set<RTLIL::SigBit> lut_inputs = cell->getPort(ID::A).to_sigbit_set();
    std::vector<RTLIL::SigBit> lut_inputs_vector =
        cell->getPort(ID::A).to_sigbit_vector();
    std::set<RTLIL::SigBit> common_port_all;
    std::vector<bool> replaced_boolean_value;
    std::vector<bool> remained_boolean_value;
    bool rewire_required = false;
    std::vector<RTLIL::State> old_lut =
        cell->parameters.at(ID::LUT).bits(); // Original LUT truth table
    for (const auto &[internal_signal_output, internal_signal_input] :
         internal_signal_io_map) {
      std::set<RTLIL::SigBit> common_port;
      std::string mapped_ckbuf_name;
      if (std::includes(lut_inputs.begin(), lut_inputs.end(),
                        internal_signal_input.begin(),
                        internal_signal_input.end())) {
        std::set_intersection(lut_inputs.begin(), lut_inputs.end(),
                              internal_signal_input.begin(),
                              internal_signal_input.end(),
                              std::inserter(common_port, common_port.end()));
        std::string C_output = internal_signal_output + "_ckbuf";
        mapped_ckbuf_name = internal_signal_output;
        if (!module->wire("\\" + C_output)) {
          log("wire %s is not defined", C_output.c_str());
        }
        auto replaced_sig = module->wire("\\" + C_output);
        if (sig.find(replaced_sig) != sig.end()) {
          /* element has already been recorded*/
          log("signal %s has been replaced!\n", C_output.c_str());
          continue;
        }
        sig.insert(replaced_sig);
        if (std::find(ordered_sig.begin(), ordered_sig.end(), replaced_sig) ==
            ordered_sig.end()) {
          ordered_sig.push_back(replaced_sig);
        }
        sig_replace_port_map[replaced_sig] = common_port;
        auto src_cell = internal_signal_lut.at(mapped_ckbuf_name);
        sig_replace_cell_map[replaced_sig] = src_cell;
        rewire_required = true;
        common_port_all.insert(common_port.begin(), common_port.end());
      }
    }

    if (rewire_required) {
      // For example, the following lut will be rewired
      //     .names a b internal_clock1
      //     .names a b c  out
      //     as
      //      .names internal_clock1_ckbuf c out
      //     where internal_clock1 is the original internal signals and
      // internal_clock1_ckbuf is the outputs of ckbuf. (.subckt ckbuf
      // internal_clock1 internal_clock1_ckbuf)
      // we need to update the truth table of .names internal_clock1_ckbuf
      // c out concurrently
      /* The first step is to get the original truth table, i.e. the truth
       * table of .names a b c d out */
      int bit_width = lut_inputs_vector.size();
      std::vector<std::vector<bool>> original_truth_table;
      std::map<RTLIL::SigBit, int> sig_index_map;

      for (size_t index = 0; index < lut_inputs_vector.size(); index++) {
        sig_index_map[lut_inputs_vector[index]] = index;
      }

      for (int index = 0; index < old_lut.size(); index++) {
        if (old_lut[index] == RTLIL::State::S1) {
          std::vector<bool> bits(bit_width, false);
          for (int b = 0; b < bit_width; b++) {
            bits[b] = (index >> b) & 1;
          }
          original_truth_table.push_back(bits);
        }
      }

      /* get remained sigs */
      std::set_difference(lut_inputs.begin(), lut_inputs.end(),
                          common_port_all.begin(), common_port_all.end(),
                          std::inserter(temp_sig, temp_sig.end()));

      std::vector<std::vector<bool>> modified_bit;

      for (const auto &line : original_truth_table) {
        std::vector<bool> remained_bit;
        /* get sigs that can be replaced by ckbuf and evaluate its truth
         * table values and updates the final truth table*/
        for (auto replaced_sig : sig) {
          const RTLIL::Cell *cell_temp =
              module->cell(sig_replace_cell_map[replaced_sig]);
          auto ports = sig_replace_port_map[replaced_sig];

          std::map<RTLIL::SigBit, bool> common_port_map;
          for (auto port : ports) {
            common_port_map[port] = line[sig_index_map[port]];
          }

          bool changed_bit = eval_lut(cell_temp, common_port_map, sigmap);
          remained_bit.push_back(changed_bit);
        }
        /* get remained sigs and use previous truth table values*/
        for (auto port : temp_sig) {
          remained_bit.push_back(line[sig_index_map[port]]);
        }

        modified_bit.push_back(remained_bit);
      }
      /* get the final truth table of the rewired lut such as .names
       * internal_clock1_ckbuf c out */
      std::vector<int> modified_bit_int;
      for (const auto &line : modified_bit) {
        int value = 0;
        for (size_t i = 0; i < line.size(); i++) {
          if (line[i]) {
            value |= (1 << i);
          }
        }
        modified_bit_int.push_back(value);
      }

      sig.insert(temp_sig.begin(), temp_sig.end());
      ordered_sig.insert(ordered_sig.end(), temp_sig.begin(), temp_sig.end());

      int new_width = sig.size();
      int num_entries = 1 << new_width;
      RTLIL::Const new_lut(num_entries);
      /*initialize lut value to 0*/
      for (int i = 0; i < num_entries; i++) {
        new_lut.bits()[i] = RTLIL::State::S0;
      }
      /* assign final truth table's info to current cell */
      for (int i : modified_bit_int) {
        new_lut.bits()[i] = RTLIL::State::S1;
      }

      rewire_lut_primitive(cell, ordered_sig, new_lut, new_width);
      module->fixup_ports();
      std::set<RTLIL::SigBit> lut_outputs =
          cell->getPort(ID::Y).to_sigbit_set();
    }
  }
  /* This function rewires luts which have internally generated signals as its
   * input*/
  void rewire_luts(RTLIL::Module *module,
                   const std::set<std::string> &ckbuf_info) {
    /* find the lut that has internally generated clock as an output and get its
     * io map */
    Yosys::SigMap sigmap(module);
    std::map<std::string, std::set<RTLIL::SigBit>> internal_signal_io_map;
    std::map<std::string, std::string> internal_signal_lut;
    std::set<RTLIL::SigBit> flattened_io_map;
    /*the first for loop constructs the map between internall signal name and
    its corresponding fan-ins For example, consider the following netlist:
        .names a b internal_clock1
        .names c d internal_clock2
    The internal_signal_io_map stores key-value pairs from all luts like this:
        [internal_clock1, {a, b}], [internal_clock2, {c, d}].
    */
    for (const auto cell : module->cells()) {
      if ((cell->type) == ID($lut)) {
        auto &inputs = cell->getPort(ID::A);
        std::string output = str(cell->getPort(ID::Y));
        auto width = cell->parameters.at(ID::WIDTH).as_int();
        log_assert(inputs.size() == width);
        if (ckbuf_info.find(output) != ckbuf_info.end()) {
          /* We assume that all LUT cells are explicitly named before the
          current pass. Anonymous cells indicate an unexpected state after
          techmapping and are treated as a fatal error. */
          if (cell->name.empty()) {
            log_error("cell->name is empty for output=%s\n", output.c_str());
          }
          auto io_set = inputs.to_sigbit_set();
          internal_signal_io_map[output] = io_set;
          internal_signal_lut[output] = cell->name.c_str();
          flattened_io_map.insert(internal_signal_io_map[output].begin(),
                                  internal_signal_io_map[output].end());
          continue;
        }
      }
    }

    /* This for loop does two things:
    1. detect logic that can be replaced by internal signals
            For example, consider the following netlist:
                .names a b internal_clock1
                .names c d internal_clock2
        The internal_signal_io_map stores key-value pairs from all luts like
    this: [internal_clock1, {a, b}], [internal_clock2, {c, d}]. When we
    encounter a netlist like: .names a b c d out we can replace it with .names
    internal_clock1 internal_clock2 out

    2. rewire luts
        For example, the following lut will be rewired
            .names internal_clock1 internal_clock2 out
        as
            .names internal_clock1_ckbuf internal_clock2_ckbuf out_ckbuf
        where internal_clock1/2 are the original internal signals and
    internal_clock1_ckbuf/2_ckbuf are the outputs of ckbuf. (.subckt ckbuf
    internal_clock1 internal_clock1_ckbuf)
         */
    for (auto cell : module->cells()) {
      if ((cell->type) == ID($lut)) {
        std::string output = str(cell->getPort(ID::Y));
        if (ckbuf_info.find(output) != ckbuf_info.end()) {
          continue; /*by pass the luts that generate internal clk/reset */
        } else {
          process_cell_rewire_lut(module, cell, internal_signal_io_map,
                                  internal_signal_lut, sigmap);
          /*replace internal clk/reset with clk/reset_buf signal */
        }
      }
    }
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override {
    log("Arguments to the command insert_clock_buffer:\n");
    std::string top_module_name;
    std::string cell_map_file;
    for (size_t i = 0; i < args.size(); i++) {
      log("  %s\n", args[i].c_str());

      if (args[i] == "-top" && i + 1 < args.size()) {
        top_module_name = args[i + 1];
      } else if (args[i] == "-cell_map_file" && i + 1 < args.size()) {
        cell_map_file = args[i + 1];
      }
    }

    if (cell_map_file.empty()) {
      cell_map_file = "cell_map.xml";
    }
    log("cell map location is %s \n", cell_map_file.c_str());

    /*if top_module_name is empty, get it from design*/
    if (top_module_name.empty())
      for (auto module : design->modules())
        if (module->get_bool_attribute(ID::top))
          top_module_name = module->name.str();

    if (top_module_name.empty()) {
      log_error("No top module detected. Insert clock buffer failed.");
    } else {
      log("Top module in current design: %s \n", top_module_name.c_str());
    }

    /*Insert clock buffer into the top module*/
    design->sort();
    for (auto module : design->modules()) {
      /*only insert buffer to top module*/
      if (module->name == RTLIL::escape_id(top_module_name)) {
        std::map<std::string, std::string> ckbuf_type;
        std::set<std::string> ckbuf_info =
            find_internal_clk_r_signal(module, ckbuf_type);
        /*insert ckbuf and rewire dff */
        insert_ckbuf(module, ckbuf_info);

        module->fixup_ports();
        /*rewire luts */
        rewire_luts(module, ckbuf_info);

        module->fixup_ports();
        /* print out cells */
        if (!ckbuf_info.empty()) {
          generate_cell_map(cell_map_file.c_str(), ckbuf_info, ckbuf_type);
        } else {
          log("Ckbuf info is empty. No cell map file will be generated! \n");
        }
        break;
      }
    }
    design->check();
  }
} Insert_clock_buffer;

PRIVATE_NAMESPACE_END
