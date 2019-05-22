#!/usr/bin/python3
import unittest
from pathlib import Path

from pyosys import libyosys as ys

verilog_content = """
module counter (clk, aload, d, b, q, qa);
input clk, aload;
input  [3:0] d;
input  [3:0] b;
output [7:0] q;
output [7:0] qa;
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
  assign qa = q;
endmodule
"""

ys_script = """
read_verilog {v_file}
prep
scatter
"""

class TestSanity(unittest.TestCase):
    @classmethod
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

    @classmethod
    def tearDownClass(cls):
      # Delete tmp files
      cls.v_file.unlink()
      cls.ys_file.unlink()
      cls.design = None

    def test_sigbits(self):
        """
        Test collect sigbits
        """
        design = TestSanity.design

        sigbit_to_driver_index = {}
        cell_stats = {}

        def get_module_ports(module):
            res = {}
            #for wire in module.wires_.items()
            return res


        for module in design.selected_whole_modules_warn():
            sigmap = ys.SigMap(module)
            for cell in module.selected_cells():
                if cell.type.str() in cell_stats:
                    cell_stats[cell.type.str()] += 1
                else:
                    cell_stats[cell.type.str()] = 1
                for conn_first, conn_second in cell.connections_.items():
                    if cell.output(conn_first):
                        dd = sigmap(conn_second).to_sigbit_vector()
                        for bit in dd:
                            sigbit_to_driver_index[bit] = cell

    def test_module_connections(self):
        """
        Test print module connections
        """
        design = TestSanity.design

        for module in design.selected_whole_modules_warn():
            sigmap = ys.SigMap(module)
            for conn_first, conn_second in module.connections_:
                # TODO: SigSpec.as_string()
                a =  sigmap(conn_first).as_string()
                self.assertNotEqual(a, "????????")
                b =  sigmap(conn_second).as_string()
                print(a, b)

    def test_module_wires(self):
        """
        Test print wires
        """
        design = TestSanity.design

        for module in design.selected_whole_modules_warn():
            sigmap = ys.SigMap(module)
            for name, wire in module.wires_.items():
                if wire.port_output:
                    print("O: ", wire)
                    # foo = sigmap(wire).to_sigbit_map()
                elif wire.port_input:
                    print("I: ", wire)
                else:
                    print("W: ", wire)

    @unittest.skip("TypeError: No to_python (by-value) converter found for C++ type: Yosys::RTLIL::SigSpec")
    def test_sigbit(self):
        """
        Test sigbit
        """
        design = TestSanity.design
        sigidcounter = 1

        for module in design.selected_whole_modules_warn():
            sigmap = ys.SigMap(module)
            for conn_first, conn_second in module.connections_:
                ff = ys.unescape_id(conn_first.name)
                sm = sigmap(conn_first).to_sigbit_vector()
                sa = sigmap(conn_first)
                # foo = sa.is_wire()
                w = []
                for bit in sm:
                    if not bit.is_wire():
                        d = bit.get_data()
                        if (d == ys.State.S0): s = '"0"'
                        elif (d == ys.State.S1): s = '"1"'
                    else:
                        s = "%s" % (sigidcounter)
                        sigidcounter +=1
                    w.append(s)
                print("Module W: ", ", ".join(w))


if __name__ == '__main__':
    unittest.main()