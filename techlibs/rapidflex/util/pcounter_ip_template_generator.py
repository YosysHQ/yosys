import time
import logging
import yaml
import os
import re
import subprocess
from datetime import timedelta
from datetime import datetime
import threading
import csv

# Constants
CLK_TYPE_RISE = "RISING"
CLK_TYPE_FALL = "FALLING"
RST_TYPE_SYNC = "SYNCHRONOUS"
RST_TYPE_ASYNC = "ASYNCHRONOUS"
RST_POLARITY_L = "ACTIVE-LOW"
RST_POLARITY_H = "ACTIVE-HIGH"
EVENT_TYPE_LOAD = "LOAD"
EVENT_TYPE_ADD = "ADD"
EVENT_TYPE_SUB = "SUBTRACT"
EVENT_TYPE_SR = "SHIFT-RIGHT"
EVENT_TYPE_SL = "SHIFT-LEFT"


# Class of an mini pin table
class PcounterIpTemplateGenerator:
    def __init__(self):
        # Constants
        self.__CLK_TYPES_ = [CLK_TYPE_RISE, CLK_TYPE_FALL]
        self.__RST_TYPES_ = [RST_TYPE_SYNC, RST_TYPE_ASYNC]
        self.__RST_POLARITIES_ = [RST_POLARITY_L, RST_POLARITY_H]
        self.__EVENT_TYPES_ = [
            EVENT_TYPE_LOAD,
            EVENT_TYPE_ADD,
            EVENT_TYPE_SUB,
            EVENT_TYPE_SR,
            EVENT_TYPE_SL,
        ]
        self.__MAX_DATA_SIZE_ = 32
        self.__CCB_POSTFIX_ = "_ccb"
        # Internal switches
        self.__include_q_ = False

    # Create a new row
    def clock_types(self):
        return self.__CLK_TYPES_

    def reset_types(self):
        return self.__RST_TYPES_

    def reset_polarities(self):
        return self.__RST_POLARITIES_

    def event_types(self):
        return self.__EVENT_TYPES_

    def data_sizes(self):
        return range(1, self.__MAX_DATA_SIZE_ + 1)

    def max_data_size(self):
        return self.__MAX_DATA_SIZE_

    def __verilog_clock_edge(self, edge_type):
        if edge_type == CLK_TYPE_RISE:
            return "posedge"
        elif edge_type == CLK_TYPE_FALL:
            return "negedge"
        else:
            raise Exception(f"Invalid clock type '{edge_type}'. Expect {self.__CLK_TYPES_}\n")

    def __verilog_reset_edge(self, edge_type):
        if edge_type == RST_POLARITY_H:
            return "posedge"
        elif edge_type == RST_POLARITY_L:
            return "negedge"
        else:
            raise Exception(f"Invalid reset type '{edge_type}'. Expect {self.__RST_POLARITIES_}\n")

    def __verilog_reset_polarity(self, polarity_type):
        if polarity_type == RST_POLARITY_L:
            return "~"
        elif polarity_type == RST_POLARITY_H:
            return ""
        else:
            raise Exception(
                f"Invalid reset type '{polarity_type}'. Expect {self.__RST_POLARITIES}\n"
            )

    def __verilog_event_op_ccb(self, event_type):
        if event_type == EVENT_TYPE_LOAD:
            return "ccb_load_val_i"
        elif event_type == EVENT_TYPE_ADD:
            return "q_o + ccb_load_val_i"
        elif event_type == EVENT_TYPE_SUB:
            return "q_o - ccb_load_val_i"
        elif event_type == EVENT_TYPE_SL:
            return "q_o << ccb_load_val_i"
        elif event_type == EVENT_TYPE_SR:
            return "q_o >> ccb_load_val_i"
        else:
            raise Exception(f"Invalid event type '{event_type}'. Expect {self.__EVENT_TYPES_}\n")

    def __verilog_event_op(self, event_type):
        if event_type == EVENT_TYPE_LOAD:
            return "LOAD_VAL"
        elif event_type == EVENT_TYPE_ADD:
            return "q_o + LOAD_VAL"
        elif event_type == EVENT_TYPE_SUB:
            return "q_o - LOAD_VAL"
        elif event_type == EVENT_TYPE_SL:
            return "q_o << LOAD_VAL"
        elif event_type == EVENT_TYPE_SR:
            return "q_o >> LOAD_VAL"
        else:
            raise Exception(f"Invalid event type '{event_type}'. Expect {self.__EVENT_TYPES_}\n")

    def __clock_type_str(self, edge_type):
        if edge_type == CLK_TYPE_RISE:
            return "clkp"
        elif edge_type == CLK_TYPE_FALL:
            return "clkn"
        else:
            raise Exception(f"Invalid clock type '{edge_type}'. Expect {self.__CLK_TYPES_}\n")

    def __reset_type_str(self, edge_type, polarity_type):
        ret = ""
        if edge_type == RST_TYPE_ASYNC:
            ret = "arst"
        elif edge_type == RST_TYPE_SYNC:
            ret = "srst"
        else:
            raise Exception(f"Invalid reset type '{edge_type}'. Expect {self.__RST_TYPES_}\n")

        if polarity_type == RST_POLARITY_L:
            ret += "n"
        elif polarity_type == RST_POLARITY_H:
            ret += "p"
        else:
            raise Exception(
                f"Invalid reset type '{polarity_type}'. Expect {self.__RST_POLARITIES}\n"
            )

        return ret

    def __event_type_str(self, event_type):
        if event_type == EVENT_TYPE_LOAD:
            return "load"
        elif event_type == EVENT_TYPE_ADD:
            return "add"
        elif event_type == EVENT_TYPE_SUB:
            return "sub"
        elif event_type == EVENT_TYPE_SL:
            return "sl"
        elif event_type == EVENT_TYPE_SR:
            return "sr"
        else:
            raise Exception(f"Invalid event type '{event_type}'. Expect {self.__EVENT_TYPES_}\n")

    def ccb_ip_template_name(self, c_type, r_type, r_polar, e_type):
        return (
            "pcounterN_"
            + self.__clock_type_str(c_type)
            + "_"
            + self.__reset_type_str(r_type, r_polar)
            + "_"
            + self.__event_type_str(e_type)
            + self.__CCB_POSTFIX_
        )

    def ip_template_name(self, c_type, r_type, r_polar, e_type):
        return (
            "pcounterN_"
            + self.__clock_type_str(c_type)
            + "_"
            + self.__reset_type_str(r_type, r_polar)
            + "_"
            + self.__event_type_str(e_type)
        )

    def ip_name(self, c_type, r_type, r_polar, e_type, d_size):
        return (
            "pcounter"
            + str(d_size)
            + "_"
            + self.__clock_type_str(c_type)
            + "_"
            + self.__reset_type_str(r_type, r_polar)
            + "_"
            + self.__event_type_str(e_type)
        )

    def ccb_ip_name(self, c_type, r_type, r_polar, e_type, d_size):
        return (
            "pcounter"
            + str(d_size)
            + "_"
            + self.__clock_type_str(c_type)
            + "_"
            + self.__reset_type_str(r_type, r_polar)
            + "_"
            + self.__event_type_str(e_type)
            + self.__CCB_POSTFIX_
        )

    def write_ccb_ip_template(self, f0, c_type, r_type, r_polar, e_type):
        f0.write("//-------------------------------------------------\n\n")
        f0.write(
            "// Template of Programmable counter to be counting up or down as well as paused\n\n"
        )
        f0.write(f"// triggered by {c_type.lower()} edge clock\n\n")
        f0.write(f"// with {r_type.lower()} {r_polar.lower()} reset\n\n")
        f0.write(f"// Capable of {e_type.lower()} values from inputs\n\n")
        f0.write("`default_nettype none\n\n")
        f0.write(f"module {self.ccb_ip_template_name(c_type, r_type, r_polar, e_type)} #(\n")
        f0.write(f"  parameter integer DATA_WIDTH = {self.__MAX_DATA_SIZE_}\n")
        f0.write(")(\n")
        f0.write("  input clk_i,\n")
        f0.write("  input rst_i,\n")
        f0.write("  input up_down_i,\n")
        f0.write("  input event_i,\n")
        f0.write("  input enable_i,\n")
        f0.write("  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,\n")
        f0.write("  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,\n")
        f0.write("  input [0 : DATA_WIDTH - 1] ccb_load_val_i,\n")
        f0.write("  output match0_o,\n")
        f0.write("  output match1_o,\n")
        f0.write("  output zero_o,\n")
        f0.write("  output [0 : DATA_WIDTH - 1] q_o\n")
        f0.write(");\n")
        f0.write("  reg [0 : DATA_WIDTH - 1] q_o;\n")

        if r_type == RST_TYPE_ASYNC:
            f0.write(
                f"  always@({self.__verilog_clock_edge(c_type)} clk_i or {self.__verilog_reset_edge(r_polar)} rst_i) \n"
            )
        elif r_type == RST_TYPE_SYNC:
            f0.write(f"  always@({self.__verilog_clock_edge(c_type)} clk_i) \n")
        else:
            raise Exception(f"Invalid reset type '{edge_type}'. Expect {self.__RST_TYPES_}\n")

        f0.write("  begin\n")
        f0.write(
            f"    if ({self.__verilog_reset_polarity(r_polar)}rst_i)    //Set Counter to Zero\n"
        )
        f0.write("      q_o <= 0;\n")
        f0.write("    else if(event_i)\n")
        f0.write(f"      q_o <= {self.__verilog_event_op_ccb(e_type)};\n")
        f0.write("    else if (~enable_i)\n")
        f0.write("      q_o <= q_o;  // pause\n")
        f0.write("    else if(up_down_i)        //count down\n")
        f0.write("      q_o <= q_o - 1;\n")
        f0.write("    else            //count up\n")
        f0.write("      q_o <= q_o + 1;\n")
        f0.write("  end\n")
        f0.write("  assign zero_o = (q_o == 0) ? 1 : 0;\n")
        f0.write("  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;\n")
        f0.write("  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;\n")
        f0.write("endmodule\n")
        f0.write("`default_nettype wire\n")

    def write_ip_template(self, f0, c_type, r_type, r_polar, e_type):
        f0.write("//-------------------------------------------------\n\n")
        f0.write(
            "// Template of Programmable counter to be counting up or down as well as paused\n\n"
        )
        f0.write(f"// triggered by {c_type.lower()} edge clock\n\n")
        f0.write(f"// with {r_type.lower()} {r_polar.lower()} reset\n\n")
        f0.write(f"// Capable of {e_type.lower()} values from inputs\n\n")
        f0.write("`default_nettype none\n\n")
        f0.write(f"module {self.ip_template_name(c_type, r_type, r_polar, e_type)} #(\n")
        f0.write(f"  parameter integer DATA_WIDTH = {self.__MAX_DATA_SIZE_},\n")
        f0.write("  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},\n")
        f0.write("  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},\n")
        f0.write("  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}\n")
        f0.write(")(\n")
        f0.write("  input clk_i,\n")
        f0.write("  input rst_i,\n")
        f0.write("  input up_down_i,\n")
        f0.write("  input event_i,\n")
        f0.write("  input enable_i,\n")
        f0.write("  output match0_o,\n")
        f0.write("  output match1_o,\n")
        f0.write("  output zero_o")
        if self.__include_q_:
            f0.write(",\n")
            f0.write("  output [0 : DATA_WIDTH - 1] q_o\n")
        f0.write(");\n")
        f0.write("  reg [0 : DATA_WIDTH - 1] q_o;\n")

        if r_type == RST_TYPE_ASYNC:
            f0.write(
                f"  always@({self.__verilog_clock_edge(c_type)} clk_i or {self.__verilog_reset_edge(r_polar)} rst_i) \n"
            )
        elif r_type == RST_TYPE_SYNC:
            f0.write(f"  always@({self.__verilog_clock_edge(c_type)} clk_i) \n")
        else:
            raise Exception(f"Invalid reset type '{edge_type}'. Expect {self.__RST_TYPES_}\n")

        f0.write("  begin\n")
        f0.write(
            f"    if ({self.__verilog_reset_polarity(r_polar)}rst_i)    //Set Counter to Zero\n"
        )
        f0.write("      q_o <= 0;\n")
        f0.write("    else if(event_i)\n")
        f0.write(f"      q_o <= {self.__verilog_event_op(e_type)};\n")
        f0.write("    else if (~enable_i)\n")
        f0.write("      q_o <= q_o;  // pause\n")
        f0.write("    else if(up_down_i)        //count down\n")
        f0.write("      q_o <= q_o - 1;\n")
        f0.write("    else            //count up\n")
        f0.write("      q_o <= q_o + 1;\n")
        f0.write("  end\n")
        f0.write("  assign zero_o = (q_o == 0) ? 1 : 0;\n")
        f0.write("  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;\n")
        f0.write("  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;\n")
        f0.write("endmodule\n")
        f0.write("`default_nettype wire\n")

    def write_ccb_ip(self, f0, c_type, r_type, r_polar, e_type, d_size, require_padding=False):
        d_msb = d_size - 1
        f0.write("`default_nettype none\n\n")
        f0.write(f"module {self.ccb_ip_name(c_type, r_type, r_polar, e_type, d_size)} # (\n")
        f0.write("  // Location constraints\n")
        f0.write("  parameter FPGA_LOC_X = 0,\n")
        f0.write("  parameter FPGA_LOC_Y = 0,\n")
        f0.write("  parameter FPGA_LOC_Z = 0)(\n")
        f0.write("  input clk_i,\n")
        f0.write("  input rst_i,\n")
        f0.write("  input up_down_i,\n")
        f0.write("  input event_i,\n")
        f0.write("  input enable_i,\n")
        f0.write(f"  input [0 : {d_msb}] ccb_match0_ref_i,\n")
        f0.write(f"  input [0 : {d_msb}] ccb_match1_ref_i,\n")
        f0.write(f"  input [0 : {d_msb}] ccb_load_val_i,\n")
        f0.write("  output match0_o,\n")
        f0.write("  output match1_o,\n")
        f0.write("  output zero_o,\n")
        f0.write(f"  output [0 : {d_msb}] q_o\n")
        f0.write(");\n")

        # Local wire
        padding_size = self.__MAX_DATA_SIZE_ - d_size
        # Padding
        # q_padding_str = "q_o"
        # if require_padding:
        #     if padding_size:
        #         q_padding_str = "{ q_o, {" + str(padding_size) + "{1'b0}} }"
        #     f0.write(f"wire [0: {self.__MAX_DATA_SIZE_ - 1}] q_wire;\n")
        #     f0.write(f"assign q_wire = {q_padding_str};\n")
        # else:
        #     f0.write(f"wire [0: {d_size - 1}] q_wire;\n")
        #     f0.write(f"assign q_wire = q_o;\n")

        f0.write(f"  {self.ccb_ip_template_name(c_type, r_type, r_polar, e_type)} #(\n")
        if require_padding:
            f0.write(f"    .DATA_WIDTH({self.__MAX_DATA_SIZE_})\n")
        else:
            f0.write(f"    .DATA_WIDTH({d_size})\n")

        load_val_padding_str = "ccb_load_val_i"
        if require_padding:
            if padding_size:
                load_val_padding_str = "{ ccb_load_val_i, {" + str(padding_size) + "{1'b0}} }"

        match0_padding_str = "ccb_match0_ref_i"
        if require_padding:
            if padding_size:
                match0_padding_str = "{ ccb_match0_ref_i, {" + str(padding_size) + "{1'b0}} }"

        match1_padding_str = "ccb_match1_ref_i"
        if require_padding:
            if padding_size:
                match1_padding_str = "{ ccb_match1_ref_i, {" + str(padding_size) + "{1'b0}} }"

        f0.write("  ) core (\n")
        f0.write("    .clk_i(clk_i),\n")
        f0.write("    .rst_i(rst_i),\n")
        f0.write("    .up_down_i(up_down_i),\n")
        f0.write("    .event_i(event_i),\n")
        f0.write("    .enable_i(enable_i),\n")
        f0.write(f"    .ccb_load_val_i({load_val_padding_str}),\n")
        f0.write(f"    .ccb_match0_ref_i({match0_padding_str}),\n")
        f0.write(f"    .ccb_match1_ref_i({match1_padding_str}),\n")
        f0.write("    .match0_o(match0_o),\n")
        f0.write("    .match1_o(match1_o),\n")
        f0.write("    .zero_o(zero_o),\n")
        f0.write(f"    .q_o(q_o)\n")

        f0.write("  );\n")
        f0.write("endmodule\n")
        f0.write("`default_nettype wire\n")

    def write_ip(self, f0, c_type, r_type, r_polar, e_type, d_size, require_padding=False):
        d_msb = d_size - 1
        f0.write("`default_nettype none\n\n")
        f0.write(f"module {self.ip_name(c_type, r_type, r_polar, e_type, d_size)} #(\n")
        f0.write("  // Location constraints\n")
        f0.write("  parameter FPGA_LOC_X = 0,\n")
        f0.write("  parameter FPGA_LOC_Y = 0,\n")
        f0.write("  parameter FPGA_LOC_Z = 0,\n")
        f0.write("  parameter [0 : " + str(d_msb) + "] LOAD_VAL = {" + str(d_size) + "{1'b0}},\n")
        f0.write("  parameter [0 : " + str(d_msb) + "] MATCH0_REF = {" + str(d_size) + "{1'b0}},\n")
        f0.write("  parameter [0 : " + str(d_msb) + "] MATCH1_REF = {" + str(d_size) + "{1'b0}}\n")
        f0.write(")(\n")
        f0.write("  input clk_i,\n")
        f0.write("  input rst_i,\n")
        f0.write("  input up_down_i,\n")
        f0.write("  input event_i,\n")
        f0.write("  input enable_i,\n")
        f0.write("  output match0_o,\n")
        f0.write("  output match1_o,\n")
        f0.write("  output zero_o")

        if self.__include_q_:
            f0.write(",\n")
            f0.write(f"  output [0 : {d_msb}] q_o\n")
        else:
            f0.write("\n")

        f0.write(");\n")

        # Local wire
        padding_size = self.__MAX_DATA_SIZE_ - d_size
        # if self.__include_q_:
        #     q_padding_str = "q_o"
        #     if require_padding:
        #         if padding_size:
        #             q_padding_str = "{ q_o, {" + str(padding_size) + "{1'b0}} }"
        #         f0.write(f"wire [0: {self.__MAX_DATA_SIZE_ - 1}] q_wire;\n")
        #         f0.write(f"assign q_wire = {q_padding_str};\n")
        #     else:
        #         f0.write(f"wire [0: {d_size - 1}] q_wire;\n")
        #         f0.write(f"assign q_wire = {q_padding_str};\n")

        f0.write(f"  {self.ip_template_name(c_type, r_type, r_polar, e_type)} #(\n")
        if require_padding:
            f0.write(f"    .DATA_WIDTH({self.__MAX_DATA_SIZE_})\n")
        else:
            f0.write(f"    .DATA_WIDTH({d_size}),\n")

        load_val_padding_str = "LOAD_VAL"
        if require_padding:
            if padding_size:
                load_val_padding_str = "{ LOAD_VAL, {" + str(padding_size) + "{1'b0}} }"
        f0.write(f"    .LOAD_VAL({load_val_padding_str}),\n")

        match0_padding_str = "MATCH0_REF"
        if require_padding:
            if padding_size:
                match0_padding_str = "{ MATCH0_REF, {" + str(padding_size) + "{1'b0}} }"
        f0.write(f"    .MATCH0_REF({match0_padding_str}),\n")

        match1_padding_str = "MATCH1_REF"
        if require_padding:
            if padding_size:
                match1_padding_str = "{ MATCH1_REF, {" + str(padding_size) + "{1'b0}} }"
        f0.write(f"    .MATCH1_REF({match1_padding_str})\n")

        f0.write("  ) core (\n")
        f0.write("    .clk_i(clk_i),\n")
        f0.write("    .rst_i(rst_i),\n")
        f0.write("    .up_down_i(up_down_i),\n")
        f0.write("    .event_i(event_i),\n")
        f0.write("    .enable_i(enable_i),\n")
        f0.write("    .match0_o(match0_o),\n")
        f0.write("    .match1_o(match1_o),\n")
        f0.write("    .zero_o(zero_o)")

        if self.__include_q_:
            f0.write(",\n")
            f0.write(f"    .q_o(q_o)\n")
        else:
            f0.write("\n")

        f0.write("  );\n")
        f0.write("endmodule\n")
        f0.write("`default_nettype wire\n")

    # Clear all the data
    def clear(self):
        self.__init__()
