Synthesis in detail
-------------------

Synthesis can generally be broken down into coarse-grain synthesis, and
fine-grain synthesis.  We saw this in :doc:`/getting_started/example_synth`
where a design was loaded and elaborated and then went through a series of
coarse-grain optimizations before being mapped to hard blocks and fine-grain
cells.  Most commands in Yosys will target either coarse-grain representation or
fine-grain representation, with only a select few compatible with both states.

Commands such as :cmd:ref:`proc`, :cmd:ref:`fsm`, and :cmd:ref:`memory` rely on
the additional information in the coarse-grain representation, along with a
number of optimizations such as :cmd:ref:`wreduce`, :cmd:ref:`share`, and
:cmd:ref:`alumacc`.  :cmd:ref:`opt` provides optimizations which are useful in
both states, while :cmd:ref:`techmap` is used to convert coarse-grain cells
to the corresponding fine-grain representation.

Single-bit cells (logic gates, FFs) as well as LUTs, half-adders, and
full-adders make up the bulk of the fine-grain representation and are necessary
for commands such as :cmd:ref:`abc`\ /:cmd:ref:`abc9`, :cmd:ref:`simplemap`,
:cmd:ref:`dfflegalize`, and :cmd:ref:`memory_map`.

.. toctree::
   :maxdepth: 3

   synth
   proc
   fsm
   memory
   opt
   techmap_synth
   extract
   abc
   cell_libs

