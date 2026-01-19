Internal cell library
=====================

The intermediate language used by Yosys (RTLIL) represents logic and memory with
a series of cells. This section provides details for those cells, breaking them
down into two major categories: coarse-grain word-level cells; and fine-grain
gate-level cells. An additional section contains a list of properties which may
be shared across multiple cells.

.. toctree::
   :maxdepth: 2

   /cell/index_word
   /cell/index_gate
   /cell/properties
