from pyosys import libyosys as ys

import json
from pathlib import Path

__file_dir__ = Path(__file__).absolute().parent

class CellStatsPass(ys.Pass):
	def __init__(self):
		super().__init__(
			"cell_stats",
			"dumps cell statistics in JSON format"
		)

	def execute(self, args, design):
		ys.log_header(design, "Dumping cell stats\n")
		ys.log_push()
		cell_stats = {}
		for module in design.all_selected_whole_modules():
			for cell in module.selected_cells():
				if cell.type.str() in cell_stats:
					cell_stats[cell.type.str()] += 1
				else:
					cell_stats[cell.type.str()] = 1
		ys.log(json.dumps(cell_stats))
		ys.log_pop()

p = CellStatsPass() # registration

design = ys.Design()
ys.run_pass(f"read_verilog {__file_dir__.parent / 'simple' / 'fiedler-cooley.v'}", design)
ys.run_pass("prep", design)
ys.run_pass("opt -full", design)
ys.run_pass("cell_stats", design)
