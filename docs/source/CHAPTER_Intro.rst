.. _chapter:intro:

Introduction
============

This document presents the Free and Open Source (FOSS) Verilog HDL synthesis
tool "Yosys". Its design and implementation as well as its performance on
real-world designs is discussed in this document.

History of Yosys
----------------

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

Structure of this document
--------------------------

The structure of this document is as follows:

:numref:`Chapter %s <chapter:intro>` is this introduction.

:numref:`Chapter %s <chapter:basics>` covers a short introduction to the world
of HDL synthesis. Basic principles and the terminology are outlined in this
chapter.

:numref:`Chapter %s <chapter:approach>` gives the quickest possible outline to
how the problem of implementing a HDL synthesis tool is approached in the case
of Yosys.

:numref:`Chapter %s <chapter:overview>` contains a more detailed overview of the
implementation of Yosys. This chapter covers the data structures used in Yosys
to represent a design in detail and is therefore recommended reading for
everyone who is interested in understanding the Yosys internals.

:numref:`Chapter %s <chapter:celllib>` covers the internal cell library used by
Yosys. This is especially important knowledge for anyone who wants to understand
the intermediate netlists used internally by Yosys.

:numref:`Chapter %s <chapter:prog>` gives a tour to the internal APIs of Yosys.
This is recommended reading for everyone who actually wants to read or write
Yosys source code. The chapter concludes with an example loadable module for
Yosys.

Chapters :numref:`%s <chapter:verilog>`, :numref:`%s <chapter:opt>` and
:numref:`%s <chapter:techmap>` cover three important pieces of the synthesis
pipeline: The Verilog frontend, the optimization passes and the technology
mapping to the target architecture, respectively.

Various appendices, including a :ref:`cmd_ref`, complete this document.

.. [#]
   A quick investigation into FOSS VHDL tools yielded similar grim results for
   FOSS VHDL synthesis tools.
