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

================================================================================
Yosys manual
================================================================================

.. toctree::
	:maxdepth: 2
	:caption: Manual
	:numbered:

	CHAPTER_Intro
	CHAPTER_Basics.rst
	CHAPTER_Approach.rst
	CHAPTER_Overview.rst
	CHAPTER_CellLib.rst
	CHAPTER_Prog.rst

	CHAPTER_Verilog.rst
	CHAPTER_Optimize.rst
	CHAPTER_Techmap.rst
	CHAPTER_Eval.rst

.. raw:: latex

	\appendix

.. toctree::
	:maxdepth: 2
	:includehidden:
	:caption: Appendix

	appendix/CHAPTER_Auxlibs.rst
	appendix/CHAPTER_Auxprogs.rst

	appendix/CHAPTER_TextRtlil.rst
	appendix/APPNOTE_010_Verilog_to_BLIF.rst 
	appendix/APPNOTE_011_Design_Investigation.rst 
	appendix/APPNOTE_012_Verilog_to_BTOR.rst
	appendix/CHAPTER_StateOfTheArt.rst

	bib

.. toctree::
	:maxdepth: 1
	:includehidden:

	cmd_ref

