#!/usr/bin/python3
import unittest
from pathlib import Path

from pyosys import libyosys as ys

verilog_content = """
module counter (clk, aload, d, b, q);
input clk, aload;
input  [3:0] d;
input  [3:0] b;
output [7:0] q;
reg    [3:0] tmp;

  always @(posedge clk)
    begin
      if (aload)
        tmp = d + b;
      else
        tmp = tmp + 1'b1;
    end
  assign q[3:0] = tmp;
  assign q[4] = 1;
  assign q[5] = d[2];
  assign q[6:7] = tmp[1:0];
endmodule
"""

ys_script = """
read_verilog {v_file}
prep
opt -full
"""

json_ref = """{
"modules": {
    "counter": {
      "attributes": {
      },
      "ports": {
        "clk": {
          "direction": "input",
          "bits": [ 2 ]
        },
        "aload": {
          "direction": "input",
          "bits": [ 3 ]
        },
        "d": {
          "direction": "input",
          "bits": [ 4, 5, 6, 7 ]
        },
        "b": {
          "direction": "input",
          "bits": [ 8, 9, 10, 11 ]
        },
        "q": {
          "direction": "output",
          "bits": [ 12, 13, 14, 15, "1", 6, 12, 13 ]
        }
      },
      "cells": {
        "$add$tmp.v:12$2": {
          "hide_name": 1,
          "type": "$add",
          "parameters": {
            "A_SIGNED": 0,
            "A_WIDTH": 4,
            "B_SIGNED": 0,
            "B_WIDTH": 4,
            "Y_WIDTH": 4
          },
          "attributes": {

          },
          "port_directions": {
            "A": "input",
            "B": "input",
            "Y": "output"
          },
          "connections": {
            "A": [ 4, 5, 6, 7 ],
            "B": [ 8, 9, 10, 11 ],
            "Y": [ 16, 17, 18, 19 ]
          }
        },
        "$add$tmp.v:14$3": {
          "hide_name": 1,
          "type": "$add",
          "parameters": {
            "A_SIGNED": 0,
            "A_WIDTH": 4,
            "B_SIGNED": 0,
            "B_WIDTH": 1,
            "Y_WIDTH": 4
          },
          "attributes": {

          },
          "port_directions": {
            "A": "input",
            "B": "input",
            "Y": "output"
          },
          "connections": {
            "A": [ 12, 13, 14, 15 ],
            "B": [ "1" ],
            "Y": [ 20, 21, 22, 23 ]
          }
        },
        "$procdff$7": {
          "hide_name": 1,
          "type": "$dff",
          "parameters": {
            "CLK_POLARITY": 1,
            "WIDTH": 4
          },
          "attributes": {

          },
          "port_directions": {
            "CLK": "input",
            "D": "input",
            "Q": "output"
          },
          "connections": {
            "CLK": [ 2 ],
            "D": [ 24, 25, 26, 27 ],
            "Q": [ 12, 13, 14, 15 ]
          }
        },
        "$procmux$5": {
          "hide_name": 1,
          "type": "$mux",
          "parameters": {
            "WIDTH": 4
          },
          "attributes": {

          },
          "port_directions": {
            "A": "input",
            "B": "input",
            "S": "input",
            "Y": "output"
          },
          "connections": {
            "A": [ 20, 21, 22, 23 ],
            "B": [ 16, 17, 18, 19 ],
            "S": [ 3 ],
            "Y": [ 24, 25, 26, 27 ]
          }
        }"""
class JSONPass():
    def get_string(self, istr):
        newstr = '"'
        for c in istr:
            if (c == '\\'):
                newstr += c
            newstr += c
        res = newstr + '"'
        return res

    def get_name(self, name):
        return self.get_string(ys.unescape_id(name))

    def get_bits(self, sig):
        sigids = self.sigids
        dd = self.sigmap(sig)
        def yield_port_strings():
            for bit in dd.to_sigbit_vector():
                if bit not in sigids.keys():
                    s = ""
                    if not bit.is_wire():
                        pass
                        if   (bit.get_data() == ys.State.S0): s = "\"0\""
                        elif (bit.get_data() == ys.State.S1): s = "\"1\""
                        elif (bit.get_data() == ys.State.Sz): s = "\"z\""
                        else: s = "\"x\""
                    else:
                        s = "%d" % (self.sigidcounter)
                        self.sigidcounter +=1
                    sigids[bit] = s
                yield sigids[bit]
        return "[ {bits} ]".format(bits=", ".join(yield_port_strings()))

    def write_parameters(self, parameters, for_module=False):
        def yield_parameters():
            for param_first, param_second in parameters.items():
                ff  = "        %s%s: " % ("" if for_module else "    ", self.get_name(param_first))
                if (param_second.flags and ys.ConstFlags.CONST_FLAG_STRING):
                    ff +=  self.get_string(param_second.decode_string())
                elif (len(param_second.bits) > 32):
                    ff +=  self.get_string(param_second.as_string())
                elif (param_second.flags and ys.ConstFlags.CONST_FLAG_SIGNED):
                    ff += "%d" % param_second.as_int()
                else:
                    ff += "%u" % param_second.as_int()
                yield ff
        return ",\n".join(yield_parameters())

    def write_module(self, module):
        self.sigmap = ys.SigMap(module)
        self.sigmap.set(module)
        self.sigids = dict() # dict<SigBit, string> sigids
        
        #  reserve 0 and 1 to avoid confusion with "0" and "1"
        self.sigidcounter = 2

        ff  = "    %s: {\n" % self.get_name(module.name)
        ff += "      \"attributes\": {"
        # TODO:
        # write_parameters(module->attributes, /*for_module=*/true);
        ff += "\n      },\n"

        def yield_port_strings():
            for port_name in module.ports:
                w = module.wire(port_name)
                tmp  = "        %s: {\n" % self.get_name(port_name)
                tmp += "          \"direction\": \"%s\",\n" % ("input" if w.port_input else "output" if w.port_output else "inout")
                tmp += "          \"bits\": %s\n" % self.get_bits(w)
                tmp += "        }"
                yield tmp
        ff += "      \"ports\": {\n"
        ff += ",\n".join(yield_port_strings())
        ff += "\n      },\n"
        ff += "      \"cells\": {\n"

        def yield_cells():
            for c in module.selected_cells():
                c_name = self.get_name(c.name)
                tff  = "        %s: {\n" % c_name
                tff += "          \"hide_name\": %s,\n" % "1" if (ys.unescape_id(c.name)[0] == '$') else "0"
                tff += "          \"type\": %s,\n" % self.get_name(c.type)
                tff += "          \"parameters\": {\n"
                tff += self.write_parameters(c.parameters)
                tff += "\n          },\n"
                tff += "          \"attributes\": {\n"
                # TODO:
                # write_parameters(c->attributes);
                tff += "\n          },\n"
                if c.known():
                    tff += "          \"port_directions\": {\n"
                    def yield_cell_ports():
                        for conn_first, conn_second in c.connections_.items():
                            direction = "output"
                            if c.input(conn_first):
                                direction = "inout" if c.output(conn_first) else "input"
                            yield "            %s: \"%s\"" % (self.get_name(conn_first), direction)
                    tff += ",\n".join(yield_cell_ports())
                    tff += "\n          },\n"
                tff += "          \"connections\": {\n"
                yc = ("            %s: %s" % (self.get_name(c_f), self.get_bits(c_s)) for c_f, c_s in c.connections_.items())
                tff += ",\n".join(yc)
                tff += "\n          }\n"
                tff += "        }"
                yield  tff
        cells = (cell for cell in yield_cells())
        ff +=  ",\n".join(cells)
        return ff
        #############

    def py_write_design(self):
        """
        Generate JSON using py_api
        """
        design = TestSanity.design
        design.sort()
        ff = "{\n"
        # TODO:
        # ff += "  \"creator\": %s,\n" % get_string(yosys_version_str).c_str()
        ff += "\"modules\": {\n"
        for module in design.selected_whole_modules_warn():
            ff += self.write_module(module)
        return ff

class TestSanity(unittest.TestCase):
    @classmethod
    @unittest.skip('AttributeError: SigBit object has no attribute is_wire')
    def setUpClass(cls):
        """
        Load design only once for all tests
        """
        def write_tmp(name, content):
            with open(name, 'wt') as tmp:
                tmp.write(content)

        # Create tmp verilog and .ys files for test
        cls.v_file = Path("./tmp.v")
        write_tmp(cls.v_file, verilog_content)
        cls.ys_file = Path("./tmp.ys")
        write_tmp(cls.ys_file, ys_script.format(v_file=cls.v_file))

        # Execute .ys file
        cls.design = ys.Design()

        ys.run_pass("script {t_ys}".format(t_ys=cls.ys_file), cls.design)
        # TODO: Fix py_wrappers attribute access
        ys.run_pass("setattr -unset src *", cls.design)
        ys.run_pass("setattr -mod -unset src *", cls.design)
        #
        cls.json_file = Path("./tmp.json")
        ys.run_pass("write_json {t_j}".format(t_j=cls.json_file), cls.design)

        cls.json_by_python = JSONPass().py_write_design()

    @classmethod
    def tearDownClass(cls):
      # Delete tmp files
      cls.v_file.unlink()
      cls.ys_file.unlink()
      cls.json_file.unlink()

    def test_write_design_ref(self):
        """
        Test with ref
        """
        self.assertEqual(self.json_by_python, json_ref)

    @unittest.skip("n")
    def test_write_design_file(self):
        """
        Test with output file
        """
        with open(self.json_file, "rt") as f:
            o_file = f.read()
        self.assertEqual(self.json_by_python, o_file)


if __name__ == '__main__':
    unittest.main()