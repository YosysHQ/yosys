#!/usr/bin/python3

from pyosys import libyosys as ys

from pathlib import Path

import matplotlib.pyplot as plt

__file_dir__ = Path(__file__).absolute().parent

class CellStatsPass(ys.Pass):

    def __init__(self):
        super().__init__("cell_stats", "Shows cell stats as plot")

    def help(self):
        ys.log("This pass uses the matplotlib library to display cell stats\n")

    def execute(self, args, design):
        ys.log_header(design, "Plotting cell stats\n")
        cell_stats = {}
        for module in design.all_selected_whole_modules():
            for cell in module.selected_cells():
                if cell.type.str() in cell_stats:
                    cell_stats[cell.type.str()] += 1
                else:
                    cell_stats[cell.type.str()] = 1
        plt.bar(range(len(cell_stats)), height = list(cell_stats.values()),align='center')
        plt.xticks(range(len(cell_stats)), list(cell_stats.keys()))
        plt.show()

    def clear_flags(self):
        ys.log("Clear Flags - CellStatsPass\n")

p = CellStatsPass() # register

if __name__ == "__main__":
    design = ys.Design()
    ys.run_pass(f"read_verilog {__file_dir__.parents[1] / 'tests' / 'simple' / 'fiedler-cooley.v'}", design)
    ys.run_pass("prep", design)
    ys.run_pass("opt -full", design)
    ys.run_pass("cell_stats", design)
