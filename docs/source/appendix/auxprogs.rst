Auxiliary programs
==================

Besides the main yosys executable, the Yosys distribution contains a set of
additional helper programs.

yosys-config
------------

The ``yosys-config`` tool (an auto-generated shell-script) can be used to query
compiler options and other information needed for building loadable modules for
Yosys. See :doc:`/yosys_internals/extending_yosys/extensions` for details.

.. literalinclude:: /generated/yosys-config
    :start-at: Usage

.. _sec:filterlib:

yosys-filterlib
---------------

.. todo:: how does a filterlib rules-file work?

The ``yosys-filterlib`` tool is a small utility that can be used to strip or
extract information from a Liberty file.  This can be useful for removing
sensitive or proprietary information such as timing or other trade secrets.

.. literalinclude:: /generated/yosys-filterlib
    :start-at: Usage

yosys-abc
---------

This is a fork of ABC with a small set of custom modifications that have not yet
been accepted upstream. Not all versions of Yosys work with all versions of ABC.
So Yosys comes with its own yosys-abc to avoid compatibility issues between the
two.

.. literalinclude:: /generated/yosys-abc
    :start-at: usage

yosys-smtbmc
------------

The ``yosys-smtbmc`` tool is a utility used by SBY for interacting with smt
solvers.

.. literalinclude:: /generated/yosys-smtbmc

yosys-witness
-------------

``yosys-witness`` is a new tool to inspect and convert yosys witness traces.
This is used in SBY and SCY for producing traces in a consistent format
independent of the solver.

.. literalinclude:: /generated/yosys-witness
    :start-at: Usage

.. note:: ``yosys-witness`` requires `click`_ Python package for use.

.. _click: https://pypi.org/project/click/
