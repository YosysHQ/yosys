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

   #. read input file to internal representation
   read_verilog design.v

   #. convert high-level behavioral parts ("processes") to d-type flip-flops and muxes
   proc

   #. perform some simple optimizations
   opt

   #. convert high-level memory constructs to d-type flip-flops and multiplexers
   memory

   #. perform some simple optimizations
   opt

   #. convert design to (logical) gate-level netlists
   techmap

   #. perform some simple optimizations
   opt

   #. map internal register types to the ones from the cell library
   dfflibmap -liberty cells.lib

   #. use ABC to map remaining logic to cells from the cell library
   abc -liberty cells.lib

   #. cleanup
   opt

   #. write results to output file
   write_verilog synth.v

A detailed description of the commands available in Yosys can be found in
:ref:`cmd_ref`.

Simple synthesis script
~~~~~~~~~~~~~~~~~~~~~~~

This section covers an example project available in
``docs/resources/PRESENTATION_Intro/*``.  The project contains a simple ASIC
synthesis script (``counter.ys``), a digital design written in Verilog
(``counter.v``), and a simple CMOS cell library (``mycells.lib``).

.. literalinclude:: ../../resources/PRESENTATION_Intro/counter.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_Intro/counter.ys``

.. role:: yoscrypt(code)
   :language: yoscrypt

#. :yoscrypt:`read_verilog counter.v` - Read Verilog source file and convert to
   internal representation.
#. :yoscrypt:`hierarchy -check -top counter` - Elaborate the design hierarchy.
   Should always be the first command after reading the design. Can re-run AST front-end.
#. :yoscrypt:`proc` - Convert ``processes`` (the internal representation of
   behavioral Verilog code) into multiplexers and registers.
#. :yoscrypt:`opt` - Perform some basic optimizations and cleanups.
#. :yoscrypt:`fsm` - Analyze and optimize finite state machines.
#. :yoscrypt:`opt` - Perform some basic optimizations and cleanups.
#. :yoscrypt:`memory` - Analyze memories and create circuits to implement them.
#. :yoscrypt:`opt` - Perform some basic optimizations and cleanups.
#. :yoscrypt:`techmap` - Map coarse-grain RTL cells (adders, etc.) to fine-grain
   logic gates (AND, OR, NOT, etc.).
#. :yoscrypt:`opt` - Perform some basic optimizations and cleanups.
#. :yoscrypt:`dfflibmap -liberty mycells.lib` - Map registers to available
   hardware flip-flops.
#. :yoscrypt:`abc -liberty mycells.lib` - Map logic to available hardware gates.
#. :yoscrypt:`clean` - Clean up the design (just the last step of
   :cmd:ref:`opt`).
#. :yoscrypt:`write_verilog synth.v` - Write final synthesis result to output
   file.

Running the script
^^^^^^^^^^^^^^^^^^

.. literalinclude:: ../../resources/PRESENTATION_Intro/counter.v
   :language: Verilog
   :caption: ``docs/resources/PRESENTATION_Intro/counter.v``

.. literalinclude:: ../../resources/PRESENTATION_Intro/mycells.lib
   :language: Liberty
   :caption: ``docs/resources/PRESENTATION_Intro/mycells.lib``

Step 1
""""""

.. literalinclude:: ../../resources/PRESENTATION_Intro/counter.ys
   :language: yoscrypt
   :lines: 1-3

Result:

.. figure:: /_images/res/PRESENTATION_Intro/counter_00.*
    :class: width-helper

Step 2
""""""

.. literalinclude:: ../../resources/PRESENTATION_Intro/counter.ys
   :language: yoscrypt
   :lines: 5-6

Result:

.. figure:: /_images/res/PRESENTATION_Intro/counter_01.*
    :class: width-helper

Step 3
""""""

.. literalinclude:: ../../resources/PRESENTATION_Intro/counter.ys
   :language: yoscrypt
   :lines: 8-9

Result:

.. figure:: /_images/res/PRESENTATION_Intro/counter_02.*
    :class: width-helper

Step 4
""""""

.. literalinclude:: ../../resources/PRESENTATION_Intro/counter.ys
   :language: yoscrypt
   :lines: 11-18

Result:

.. figure:: /_images/res/PRESENTATION_Intro/counter_03.*
    :class: width-helper
