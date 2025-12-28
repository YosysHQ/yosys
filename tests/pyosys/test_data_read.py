from pyosys import libyosys as ys
from pathlib import Path

__file_dir__ = Path(__file__).absolute().parent

d = ys.Design()

ys.run_pass(f"read_verilog {__file_dir__ / 'spm.cut.v.gz'}", d)
ys.run_pass("hierarchy -top spm", d)

name_by_tv_location = []
name_by_au_location = []

# test both dictionary mapping and equiv operators working fine
module = None
print(d.modules_)
for idstr, module_obj in d.modules_.items():
	if idstr != ys.IdString("\\spm"):
		continue
	if idstr.str() != "\\spm":
		continue
	module = module_obj
	break

assert module == d.top_module(), "top module search failed"
for name in module.ports:
	wire = module.wires_[name]
	name_str = name.str()
	if name_str.endswith(".d"):  # single reg output, in au
		name_by_au_location.append(name_str[1:-2])
	elif name_str.endswith(".q"):  # single reg input, in tv
		name_by_tv_location.append(name_str[1:-2])
	else:  # port/boundary scan
		frm = wire.start_offset + wire.width
		to = wire.start_offset
		for i in range(frm - 1, to - 1, -1):
			bit_name = name_str[1:] + f"\\[{i}\\]"
			if wire.port_input:
				name_by_tv_location.append(bit_name)
			elif wire.port_output:
				name_by_au_location.append(bit_name)

assert name_by_tv_location == ['x\\[0\\]', 'a\\[31\\]', 'a\\[30\\]', 'a\\[29\\]', 'a\\[28\\]', 'a\\[27\\]', 'a\\[26\\]', 'a\\[25\\]', 'a\\[24\\]', 'a\\[23\\]', 'a\\[22\\]', 'a\\[21\\]', 'a\\[20\\]', 'a\\[19\\]', 'a\\[18\\]', 'a\\[17\\]', 'a\\[16\\]', 'a\\[15\\]', 'a\\[14\\]', 'a\\[13\\]', 'a\\[12\\]', 'a\\[11\\]', 'a\\[10\\]', 'a\\[9\\]', 'a\\[8\\]', 'a\\[7\\]', 'a\\[6\\]', 'a\\[5\\]', 'a\\[4\\]', 'a\\[3\\]', 'a\\[2\\]', 'a\\[1\\]', 'a\\[0\\]', '_315_', '_314_', '_313_', '_312_', '_311_', '_310_', '_309_', '_308_', '_307_', '_306_', '_305_', '_304_', '_303_', '_302_', '_301_', '_300_', '_299_', '_298_', '_297_', '_296_', '_295_', '_294_', '_293_', '_292_', '_291_', '_290_', '_289_', '_288_', '_287_', '_286_', '_285_', '_284_', '_283_', '_282_', '_281_', '_280_', '_279_', '_278_', '_277_', '_276_', '_275_', '_274_', '_273_', '_272_', '_271_', '_270_', '_269_', '_268_', '_267_', '_266_', '_265_', '_264_', '_263_', '_262_', '_261_', '_260_', '_259_', '_258_', '_257_', '_256_', '_255_', '_254_', '_253_', '_252_'], "failed to extract test vector register locations"
assert name_by_au_location == ['y\\[0\\]', '_315_', '_314_', '_313_', '_312_', '_311_', '_310_', '_309_', '_308_', '_307_', '_306_', '_305_', '_304_', '_303_', '_302_', '_301_', '_300_', '_299_', '_298_', '_297_', '_296_', '_295_', '_294_', '_293_', '_292_', '_291_', '_290_', '_289_', '_288_', '_287_', '_286_', '_285_', '_284_', '_283_', '_282_', '_281_', '_280_', '_279_', '_278_', '_277_', '_276_', '_275_', '_274_', '_273_', '_272_', '_271_', '_270_', '_269_', '_268_', '_267_', '_266_', '_265_', '_264_', '_263_', '_262_', '_261_', '_260_', '_259_', '_258_', '_257_', '_256_', '_255_', '_254_', '_253_', '_252_'], "failed to extract golden output register locations"
print("ok!")
