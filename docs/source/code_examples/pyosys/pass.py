from pyosys import libyosys as ys

class AllEnablePass(ys.Pass):
	def __init__(self):
		super().__init__(
			"all_enable",
			"makes all _DFF_P_ registers require an enable signal"
		)

	def execute(self, args, design):
		ys.log_header(design, "Adding enable signals\n")
		ys.log_push()
		top_module = design.top_module()

		if "\\enable" not in top_module.wires_:
			enable_line = top_module.addWire("\\enable")
			enable_line.port_input = True
			top_module.fixup_ports()

		for cell in top_module.cells_.values():
			if cell.type != "$_DFF_P_":
				continue
			cell.type = "$_DFFE_PP_"
			cell.setPort("\\E", ys.SigSpec(enable_line))
		ys.log_pop()

p = AllEnablePass() # register the pass

# using the pass

design = ys.Design()
ys.run_pass("read_verilog tests/simple/fiedler-cooley.v", design)
ys.run_pass("hierarchy -check -auto-top", design)
ys.run_pass("synth", design)
ys.run_pass("all_enable", design)
ys.run_pass("write_verilog out.v", design)
ys.run_pass("synth_ice40 -json out.json", design)
