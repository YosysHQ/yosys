.. _sec:celllib_gates:

Gate-level cells
----------------

For gate level logic networks, fixed function single bit cells are used that do
not provide any parameters.

Simulation models for these cells can be found in the file
:file:`techlibs/common/simcells.v` in the Yosys source tree.

In most cases gate level logic networks are created from RTL networks using the
techmap pass. The flip-flop cells from the gate level logic network can be
mapped to physical flip-flop cells from a Liberty file using the dfflibmap pass.
The combinatorial logic cells can be mapped to physical cells from a Liberty
file via ABC using the abc pass.

.. toctree::
   :maxdepth: 2

   /cell/gate_comb_simple
   /cell/gate_comb_combined
   /cell/gate_reg_ff
   /cell/gate_reg_latch
   /cell/gate_other
