Auxiliary programs
==================

.. todo:: check this list is up to date and correct, esp yosys-smtbmc

Besides the main yosys executable, the Yosys distribution contains a set of
additional helper programs.

yosys-config
------------

The yosys-config tool (an auto-generated shell-script) can be used to query
compiler options and other information needed for building loadable modules for
Yosys. See :ref:`chapter:prog` for details.

.. _sec:filterlib:

yosys-filterlib
---------------

The yosys-filterlib tool is a small utility that can be used to strip or extract
information from a Liberty file. See :ref:`sec:techmap_extern` for
details.

yosys-abc
---------

This is a fork of ABC with a small set of custom modifications that have not yet
been accepted upstream. Not all versions of Yosys work with all versions of ABC.
So Yosys comes with its own yosys-abc to avoid compatibility issues between the
two.

yosys-smtbmc
------------

yosys-witness
-------------

yosys-witness is a new tool to inspect and convert yosys witness traces.
