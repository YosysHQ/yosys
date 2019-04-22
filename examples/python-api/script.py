#!/usr/bin/python3

from pyosys import libyosys as ys

import matplotlib.pyplot as plt
import numpy as np

design = ys.Design()
ys.run_pass("read_verilog ../../tests/simple/fiedler-cooley.v", design);
ys.run_pass("prep", design)
ys.run_pass("opt -full", design)

cell_stats = {}
for module in design.selected_whole_modules_warn():
  for cell in module.selected_cells():
    if cell.type.str() in cell_stats:
      cell_stats[cell.type.str()] += 1
    else:
      cell_stats[cell.type.str()] = 1
plt.bar(range(len(cell_stats)), height = list(cell_stats.values()),align='center')
plt.xticks(range(len(cell_stats)), list(cell_stats.keys()))
plt.show()
