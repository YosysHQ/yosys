Auxiliary programs
==================

Besides the main yosys executable, the Yosys distribution contains a set of
additional helper programs.

yosys-config
------------

The yosys-config tool (an auto-generated shell-script) can be used to query
compiler options and other information needed for building loadable modules for
Yosys. See Sec. \ :numref:`chapter:prog` for details.

.. _sec:filterlib:

yosys-filterlib
---------------

The yosys-filterlib tool is a small utility that can be used to strip or extract
information from a Liberty file. See :numref:`Sec. %s <sec:techmap_extern>` for
details.

yosys-abc
---------

This is a fork of ABC with a small set of custom modifications that have not yet
been accepted upstream. Not all versions of Yosys work with all versions of ABC.
So Yosys comes with its own yosys-abc to avoid compatibility issues between the
two.
