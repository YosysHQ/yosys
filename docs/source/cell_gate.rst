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
   :caption: Gate-level cells
   :maxdepth: 2

   /cell/gate_comb_simple
   /cell/gate_comb_combined
   /cell/gate_reg_ff
   /cell/gate_reg_latch

.. TODO:: Find a home for `$_TBUF_`

.. this should raise a warning, otherwise there are gate-level cells without a
   'group' tag

.. autocellgroup:: gate_other
   :caption: Other gate-level cells
   :members:
   :source:
   :linenos:
