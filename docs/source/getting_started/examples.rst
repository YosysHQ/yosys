Example(s)
----------

.. _sec:typusecase:

Typical use case
~~~~~~~~~~~~~~~~

The following example script may be used in a synthesis flow to convert the
behavioural Verilog code from the input file design.v to a gate-level netlist
synth.v using the cell library described by the Liberty file :

.. code:: yoscrypt
   :number-lines:

   # read input file to internal representation
   read_verilog design.v

   # convert high-level behavioral parts ("processes") to d-type flip-flops and muxes
   proc

   # perform some simple optimizations
   opt

   # convert high-level memory constructs to d-type flip-flops and multiplexers
   memory

   # perform some simple optimizations
   opt

   # convert design to (logical) gate-level netlists
   techmap

   # perform some simple optimizations
   opt

   # map internal register types to the ones from the cell library
   dfflibmap -liberty cells.lib

   # use ABC to map remaining logic to cells from the cell library
   abc -liberty cells.lib

   # cleanup
   opt

   # write results to output file
   write_verilog synth.v

A detailed description of the commands available in Yosys can be found in
:ref:`cmd_ref`.
