What is Yosys
=============

Yosys began as a BSc thesis project by Claire Wolf intended to support synthesis
for a CGRA (coarse-grained reconfigurable architecture).  It then expanded into
more general infrastructure for research on synthesis.

Modern Yosys has full support for the synthesizable subset of Verilog-2005 and
has been described as "the GCC of hardware synthesis."  Freely available and
`open source`_, Yosys finds use across hobbyist and commercial applications as
well as academic.

.. _open source: https://github.com/YosysHQ/yosys

.. note:: Yosys is released under the ISC License:

   A permissive license lets people do anything with your code with proper
   attribution and without warranty. The ISC license is functionally equivalent
   to the BSD 2-Clause and MIT licenses, removing some language that is no
   longer necessary.

Together with the place and route tool `nextpnr`_, Yosys can be used to program
some FPGAs with a fully end-to-end open source flow (Lattice iCE40 and ECP5). It
also does the synthesis portion for the `OpenLane flow`_, targeting the SkyWater
130nm open source PDK for fully open source ASIC design.  Yosys can also do
formal verification with backends for solver formats like `SMT2`_.

.. _nextpnr: https://github.com/YosysHQ/nextpnr
.. _OpenLane flow: https://github.com/The-OpenROAD-Project/OpenLane
.. _SMT2: https://smtlib.cs.uiowa.edu/

Yosys, and the accompanying Open Source EDA ecosystem, is currently maintained
by `Yosys Headquarters`_, with many of the core developers employed by `YosysHQ
GmbH`_.  A commercial extension, `Tabby CAD Suite`_, includes the Verific
frontend for industry-grade SystemVerilog and VHDL support, formal verification
with SVA, and formal apps.

.. _Yosys Headquarters: https://github.com/YosysHQ
.. _YosysHQ GmbH: https://www.yosyshq.com/about
.. _Tabby CAD Suite: https://www.yosyshq.com/tabby-cad-datasheet

.. figure:: /_static/logo.png
    :class: width-helper

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

  - Check out `nextpnr`_ for that

.. todo:: nextpnr for FPGAs, consider mentioning openlane, vpr, coriolis

.. _nextpnr: https://github.com/YosysHQ/nextpnr

The Yosys family
----------------

As mentioned above, `YosysHQ`_ maintains not just Yosys but an entire family of
tools built around it.  In no particular order:

.. _YosysHQ: https://github.com/YosysHQ

SBY for formal verification
   Yosys provides input parsing and conversion to the formats used by the solver
   engines.  Yosys also provides a unified witness framework for providing cover
   traces and counter examples for engines which don't natively support this.
   `SBY source`_ | `SBY docs`_

.. _SBY source: https://github.com/YosysHQ/sby
.. _SBY docs: https://yosyshq.readthedocs.io/projects/sby

EQY for equivalence checking
   In addition to input parsing and preparation, Yosys provides  the plugin
   support enabling EQY to operate on designs directly. `EQY source`_ | `EQY
   docs`_

.. _EQY source: https://github.com/YosysHQ/eqy
.. _EQY docs: https://yosyshq.readthedocs.io/projects/eqy

MCY for mutation coverage
   Yosys is used to read the source design, generate a list of possible
   mutations to maximise design coverage, and then perform selected mutations.
   `MCY source`_ | `MCY docs`_

.. _MCY source: https://github.com/YosysHQ/mcy
.. _MCY docs: https://yosyshq.readthedocs.io/projects/mcy

SCY for deep formal traces
   Since SCY generates and runs SBY, Yosys provides the same utility for SCY as
   it does for SBY.  Yosys additionally provides the trace concatenation needed
   for outputting the deep traces. `SCY source`_

.. _SCY source: https://github.com/YosysHQ/scy

The original thesis abstract
----------------------------

The first version of the Yosys documentation was published as a bachelor thesis
at the Vienna University of Technology :cite:p:`BACC`.

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

Yosys is a Verilog HDL synthesis tool. This means that it takes a behavioural
design description as input and generates an RTL, logical gate or physical gate
level description of the design as output. Yosys' main strengths are behavioural
and RTL synthesis. A wide range of commands (synthesis passes) exist within
Yosys that can be used to perform a wide range of synthesis tasks within the
domain of behavioural, rtl and logic synthesis. Yosys is designed to be
extensible and therefore is a good basis for implementing custom synthesis tools
for specialised tasks.

.. figure:: /_images/primer/levels_of_abstraction.*
    :class: width-helper invert-helper
    :name: fig:Levels_of_abstraction

    Where Yosys exists in the layers of abstraction

Benefits of open source HDL synthesis
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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

History of Yosys
~~~~~~~~~~~~~~~~

.. todo:: Consider a less academic version of the History of Yosys

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
