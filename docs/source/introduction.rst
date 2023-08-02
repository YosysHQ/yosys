What is Yosys
=============

.. TODO: rewrite to not be a thesis abstract

:Abstract:
	Most of today's digital design is done in HDL code (mostly Verilog or 
	VHDL) and with the help of HDL synthesis tools.

	In special cases such as synthesis for coarse-grain cell libraries or
	when testing new synthesis algorithms it might be necessary to write a
	custom HDL synthesis tool or add new features to an existing one. In
	these cases the availability of a Free and Open Source (FOSS) synthesis
	tool that can be used as basis for custom tools would be helpful.

	In the absence of such a tool, the Yosys Open SYnthesis Suite (Yosys)
	was developed. This document covers the design and implementation of
	this tool. At the moment the main focus of Yosys lies on the high-level
	aspects of digital synthesis. The pre-existing FOSS logic-synthesis tool
	ABC is used by Yosys to perform advanced gate-level optimizations.

	An evaluation of Yosys based on real-world designs is included. It is
	shown that Yosys can be used as-is to synthesize such designs. The
	results produced by Yosys in this tests where successfully verified
	using formal verification and are comparable in quality to the results
	produced by a commercial synthesis tool.

	This document was originally published as bachelor thesis at the Vienna
	University of Technology :cite:p:`BACC`.

Yosys is a Verilog HDL synthesis tool. This means that it takes a behavioural
design description as input and generates an RTL, logical gate or physical gate
level description of the design as output. Yosys' main strengths are behavioural
and RTL synthesis. A wide range of commands (synthesis passes) exist within
Yosys that can be used to perform a wide range of synthesis tasks within the
domain of behavioural, rtl and logic synthesis. Yosys is designed to be
extensible and therefore is a good basis for implementing custom synthesis tools
for specialised tasks.

.. figure:: ../images/levels_of_abstraction.*
    :class: width-helper
    :name: fig:Levels_of_abstraction

    Where Yosys exists in the layers of abstraction

What you can do with Yosys
--------------------------

- Read and process (most of) modern Verilog-2005 code
- Perform all kinds of operations on netlist (RTL, Logic, Gate)
- Perform logic optimizations and gate mapping with ABC

Typical applications for Yosys
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- Synthesis of final production designs
- Pre-production synthesis (trial runs before investing in other tools)
- Conversion of full-featured Verilog to simple Verilog
- Conversion of Verilog to other formats (BLIF, BTOR, etc)
- Demonstrating synthesis algorithms (e.g. for educational purposes)
- Framework for experimenting with new algorithms
- Framework for building custom flows (Not limited to synthesis but also formal
  verification, reverse engineering, ...)

Things you can't do
~~~~~~~~~~~~~~~~~~~

- Process high-level languages such as C/C++/SystemC
- Create physical layouts (place&route)
  + Check out `nextpnr`_ for that

.. _nextpnr: https://github.com/YosysHQ/nextpnr

Benefits of open source HDL synthesis
-------------------------------------

- Cost (also applies to ``free as in free beer`` solutions): 
  
  Today the cost for a mask set in 180nm technology is far less than
  the cost for the design tools needed to design the mask layouts. Open Source
  ASIC flows are an important enabler for ASIC-level Open Source Hardware.

- Availability and Reproducibility: 
  
  If you are a researcher who is publishing, you want to use tools that everyone
  else can also use. Even if most universities have access to all major
  commercial tools, you usually do not have easy access to the version that was
  used in a research project a couple of years ago. With Open Source tools you
  can even release the source code of the tool you have used alongside your data.

- Framework: 
  
  Yosys is not only a tool. It is a framework that can be used as basis for other
  developments, so researchers and hackers alike do not need to re-invent the
  basic functionality. Extensibility was one of Yosys' design goals.

- All-in-one: 
  
  Because of the framework characteristics of Yosys, an increasing number of features
  become available in one tool. Yosys not only can be used for circuit synthesis but
  also for formal equivalence checking, SAT solving, and for circuit analysis, to
  name just a few other application domains. With proprietary software one needs to
  learn a new tool for each of these applications.

- Educational Tool: 
  
  Proprietary synthesis tools are at times very secretive about their inner
  workings. They often are ``black boxes``. Yosys is very open about its
  internals and it is easy to observe the different steps of synthesis.

.. note:: Yosys is licensed under the ISC license:
   Permission to use, copy, modify, and/or distribute this software for any
   purpose with or without fee is hereby granted, provided that the above
   copyright notice and this permission notice appear in all copies.

The extended Yosys universe
---------------------------

In no particular order:

- SBY for formal verification
- EQY for equivalence checking
- MCY for mutation coverage

History of Yosys
----------------

.. TODO: copypaste

A Hardware Description Language (HDL) is a computer language used to describe
circuits. A HDL synthesis tool is a computer program that takes a formal
description of a circuit written in an HDL as input and generates a netlist that
implements the given circuit as output.

Currently the most widely used and supported HDLs for digital circuits are
Verilog :cite:p:`Verilog2005,VerilogSynth` and :abbr:`VHDL (VHSIC HDL, where
VHSIC is an acronym for Very-High-Speed Integrated Circuits)`
:cite:p:`VHDL,VHDLSynth`. Both HDLs are used for test and verification purposes
as well as logic synthesis, resulting in a set of synthesizable and a set of
non-synthesizable language features. In this document we only look at the
synthesizable subset of the language features.

In recent work on heterogeneous coarse-grain reconfigurable logic
:cite:p:`intersynth` the need for a custom application-specific HDL synthesis
tool emerged. It was soon realised that a synthesis tool that understood Verilog
or VHDL would be preferred over a synthesis tool for a custom HDL. Given an
existing Verilog or VHDL front end, the work for writing the necessary
additional features and integrating them in an existing tool can be estimated to
be about the same as writing a new tool with support for a minimalistic custom
HDL.

The proposed custom HDL synthesis tool should be licensed under a Free and Open
Source Software (FOSS) licence. So an existing FOSS Verilog or VHDL synthesis
tool would have been needed as basis to build upon. The main advantages of
choosing Verilog or VHDL is the ability to synthesize existing HDL code and to
mitigate the requirement for circuit-designers to learn a new language. In order
to take full advantage of any existing FOSS Verilog or VHDL tool, such a tool
would have to provide a feature-complete implementation of the synthesizable HDL
subset.

Basic RTL synthesis is a well understood field :cite:p:`LogicSynthesis`. Lexing,
parsing and processing of computer languages :cite:p:`Dragonbook` is a
thoroughly researched field. All the information required to write such tools
has been openly available for a long time, and it is therefore likely that a
FOSS HDL synthesis tool with a feature-complete Verilog or VHDL front end must
exist which can be used as a basis for a custom RTL synthesis tool.

Due to the author's preference for Verilog over VHDL it was decided early on to
go for Verilog instead of VHDL [#]_. So the existing FOSS Verilog synthesis
tools were evaluated. The results of this evaluation are utterly devastating.
Therefore a completely new Verilog synthesis tool was implemented and is
recommended as basis for custom synthesis tools. This is the tool that is
discussed in this document.

.. [#]
   A quick investigation into FOSS VHDL tools yielded similar grim results for
   FOSS VHDL synthesis tools.
