from pyosys import libyosys as ys

# loading design
design = ys.Design()

ys.run_pass("read_verilog tests/simple/fiedler-cooley.v", design)
ys.run_pass("hierarchy -check -auto-top", design)

# top module inspection
top_module = design.top_module()

for id, wire in top_module.wires_.items():
	if not wire.port_input and not wire.port_output:
		continue
	description = "input" if wire.port_input else "output"
	description += " " + wire.name.str()
	if wire.width != 1:
		frm = wire.start_offset
		to = wire.start_offset + wire.width
		if wire.upto:
			to, frm = frm, to
		description += f" [{to}:{frm}]"
	print(description)

# synth

ys.run_pass("synth", design)

# adding the enable line

enable_line = top_module.addWire("\\enable")
enable_line.port_input = True
top_module.fixup_ports()

# hooking the enable line to the internal dff cells

for cell in top_module.cells_.values():
	if cell.type != "$_DFF_P_":
		continue
	cell.type = "$_DFFE_PP_"
	cell.setPort("\\E", ys.SigSpec(enable_line))

# run check

top_module.check()
ys.run_pass("stat", design)

# write outputs

ys.run_pass("write_verilog out.v", design)
ys.run_pass("synth_ice40 -json out.json", design)
