.. _chapter:overview:

Yosys internals
===============

.. todo:: less academic

Yosys is an extensible open source hardware synthesis tool. It is aimed at
designers who are looking for an easily accessible, universal, and
vendor-independent synthesis tool, as well as scientists who do research in
electronic design automation (EDA) and are looking for an open synthesis
framework that can be used to test algorithms on complex real-world designs.

Yosys can synthesize a large subset of Verilog 2005 and has been tested with a
wide range of real-world designs, including the `OpenRISC 1200 CPU`_, the
`openMSP430 CPU`_, the `OpenCores I2C master`_, and the `k68 CPU`_.

.. todo:: add RISC-V core example

.. _OpenRISC 1200 CPU: https://github.com/openrisc/or1200

.. _openMSP430 CPU: http://opencores.org/projects/openmsp430

.. _OpenCores I2C master: http://opencores.org/projects/i2c

.. _k68 CPU: http://opencores.org/projects/k68

Yosys is written in C++, targeting C++17 at minimum. This chapter describes some
of the fundamental Yosys data structures. For the sake of simplicity the C++
type names used in the Yosys implementation are used in this chapter, even
though the chapter only explains the conceptual idea behind it and can be used
as reference to implement a similar system in any language.

.. toctree::
   :maxdepth: 3

   flow/index
   formats/index
   extending_yosys/index
   techmap
