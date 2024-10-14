Word-level cells
----------------

Most of the RTL cells closely resemble the operators available in HDLs such as
Verilog or VHDL. Therefore Verilog operators are used in the following sections
to define the behaviour of the RTL cells.

Note that all RTL cells have parameters indicating the size of inputs and
outputs. When passes modify RTL cells they must always keep the values of these
parameters in sync with the size of the signals connected to the inputs and
outputs.

Simulation models for the RTL cells can be found in the file
:file:`techlibs/common/simlib.v` in the Yosys source tree.

.. toctree::
   :maxdepth: 2

   /cell/word_unary
   /cell/word_binary
   /cell/word_mux
   /cell/word_reg
   /cell/word_mem
   /cell/word_fsm
   /cell/word_arith
   /cell/word_logic
   /cell/word_spec
   /cell/word_formal
   /cell/word_debug
   /cell/word_wire
