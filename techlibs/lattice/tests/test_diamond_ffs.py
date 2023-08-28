import os
import subprocess

if not os.path.exists("work_ff"):
	os.mkdir("work_ff")

modules = []

with open("../cells_ff.vh", "r") as f:
	with open("work_ff/cells_ff_gate.v", "w") as g:
		for line in f:
			if not line.startswith("module"):
				g.write(line)
				continue
			else:
				spidx = line.find(" ")
				bridx = line.find("(")
				modname = line[spidx+1 : bridx]
				g.write("module %s_gate" % modname)
				g.write(line[bridx:])
				inpidx = line.find("input ")
				outpidx = line.find(", output")
				modules.append((modname, [x.strip() for x in line[inpidx+6:outpidx].split(",")]))

with open("work_ff/testbench.v", "w") as f:
	print("""
`timescale 1ns/ 1ps

module testbench;
reg pur = 0, clk, rst, cen, d;

// Needed for Diamond sim models
GSR GSR_INST (.GSR(1'b1));
PUR PUR_INST (.PUR(pur));


initial begin
	$dumpfile("work_ff/ffs.vcd");
	$dumpvars(0, testbench);
	#5;
	pur = 1;
	#95;
	repeat (2500) begin
		{clk, rst, cen, d} = $random;
		#10;
		check_outputs;
		#1;
	end
	$finish;
end
	""", file=f)

	for modname, inputs in modules:
		print("    wire %s_gold_q, %s_gate_q;"  % (modname, modname), file=f)
		portconns = []
		for inp in inputs:
			if inp in ("SCLK", "CK"):
				portconns.append(".%s(clk)" % inp)
			elif inp in ("CD", "PD"):
				portconns.append(".%s(rst)" % inp)
			elif inp == "SP":
				portconns.append(".%s(cen)" % inp)
			elif inp == "D":
				portconns.append(".%s(d)" % inp)
			else:
				assert False
		portconns.append(".Q(%s_gold_q)" % modname)
		print("    %s %s_gold_i (%s);" % (modname, modname, ", ".join(portconns)), file=f)
		portconns[-1] = (".Q(%s_gate_q)" % modname)
		print("    %s_gate %s_gate_i (%s);" % (modname, modname, ", ".join(portconns)), file=f)
		print("", file=f)
	print("    task check_outputs;", file=f)
	print("        begin", file=f)
	print("             if (%s_gold_q != %s_gate_q) $display(\"MISMATCH at %%1t:  %s_gold_q=%%b, %s_gate_q=%%b\", $time, %s_gold_q, %s_gate_q);" %
			(modname, modname, modname, modname, modname, modname), file=f)
	print("        end", file=f)
	print("    endtask", file=f)
	print("endmodule", file=f)

diamond_models = "/usr/local/diamond/3.10_x64/cae_library/simulation/verilog/ecp5u"
subprocess.call(["iverilog", "-s", "testbench", "-o", "work_ff/testbench", "-Dmixed_hdl", "-DNO_INCLUDES", "-y", diamond_models, "work_ff/cells_ff_gate.v", "../cells_sim.v", "work_ff/testbench.v"])
subprocess.call(["vvp", "work_ff/testbench"])
