Flow overview
=============

.. todo:: less academic

:numref:`Figure %s <fig:Overview_flow>` shows the simplified data flow within
Yosys. Rectangles in the figure represent program modules and ellipses internal
data structures that are used to exchange design data between the program
modules.

Design data is read in using one of the frontend modules. The high-level HDL
frontends for Verilog and VHDL code generate an abstract syntax tree (AST) that
is then passed to the AST frontend. Note that both HDL frontends use the same
AST representation that is powerful enough to cover the Verilog HDL and VHDL
language.

The AST Frontend then compiles the AST to Yosys's main internal data format, the
RTL Intermediate Language (RTLIL). A more detailed description of this format is
given in :doc:`/yosys_internals/formats/rtlil_rep`.

There is also a text representation of the RTLIL data structure that can be
parsed using the RTLIL Frontend which is described in
:doc:`/yosys_internals/formats/rtlil_text`.

The design data may then be transformed using a series of passes that all
operate on the RTLIL representation of the design.

Finally the design in RTLIL representation is converted back to text by one of
the backends, namely the Verilog Backend for generating Verilog netlists and the
RTLIL Backend for writing the RTLIL data in the same format that is understood
by the RTLIL Frontend.

With the exception of the AST Frontend, which is called by the high-level HDL
frontends and can't be called directly by the user, all program modules are
called by the user (usually using a synthesis script that contains text commands
for Yosys).

By combining passes in different ways and/or adding additional passes to Yosys
it is possible to adapt Yosys to a wide range of applications. For this to be
possible it is key that (1) all passes operate on the same data structure
(RTLIL) and (2) that this data structure is powerful enough to represent the
design in different stages of the synthesis.

.. figure:: /_images/internals/overview_flow.*
	:class: width-helper invert-helper
	:name: fig:Overview_flow

	Yosys simplified data flow (ellipses: data structures, rectangles:
	program modules)
