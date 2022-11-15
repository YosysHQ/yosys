.. _chapter:prog:

Programming Yosys extensions
============================

This chapter contains some bits and pieces of information about
programming yosys extensions. Also consult the section on programming in
the "Yosys Presentation" (can be downloaded from the Yosys website as
PDF) and don't be afraid to ask questions on the YosysHQ Slack.

Guidelines
----------

The guidelines directory contains notes on various aspects of Yosys
development. The files GettingStarted and CodingStyle may be of
particular interest, and are reproduced here.

.. literalinclude:: ../../guidelines/GettingStarted
	:language: none
	:caption: guidelines/GettingStarted

.. literalinclude:: ../../guidelines/CodingStyle
	:language: none
	:caption: guidelines/CodingStyle

The "stubsnets" example module
------------------------------

The following is the complete code of the "stubsnets" example module. It
is included in the Yosys source distribution as
manual/CHAPTER_Prog/stubnets.cc.

.. literalinclude:: ../../manual/CHAPTER_Prog/stubnets.cc
	:language: c++
	:linenos:
	:caption: manual/CHAPTER_Prog/stubnets.cc

.. literalinclude:: ../../manual/CHAPTER_Prog/Makefile
	:language: makefile
	:linenos:
	:caption: manual/CHAPTER_Prog/Makefile

.. literalinclude:: ../../manual/CHAPTER_Prog/test.v
	:language: verilog
	:linenos:
	:caption: manual/CHAPTER_Prog/test.v
