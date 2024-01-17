Auxiliary libraries
===================

The Yosys source distribution contains some auxiliary libraries that are
compiled into Yosys and can be used in plugins.

BigInt
------

The files in ``libs/bigint/`` provide a library for performing arithmetic with
arbitrary length integers. It is written by Matt McCutchen.

The BigInt library is used for evaluating constant expressions, e.g. using the
ConstEval class provided in kernel/consteval.h.

See also: http://mattmccutchen.net/bigint/

dlfcn-win32
-----------

The ``dlfcn`` library enables runtime loading of plugins without requiring
recompilation of Yosys.  The files in ``libs/dlfcn-win32`` provide an
implementation of ``dlfcn`` for Windows.

See also: https://github.com/dlfcn-win32/dlfcn-win32

ezSAT
-----

The files in ``libs/ezsat`` provide a library for simplifying generating CNF
formulas for SAT solvers. It also contains bindings of MiniSAT. The ezSAT
library is written by C. Wolf. It is used by the :cmd:ref:`sat` pass (see
:doc:`/cmd/sat`).

fst
---

``libfst`` files from `gtkwave`_ are included in ``libs/fst`` to support
reading/writing signal traces from/to the GTKWave developed FST format.  This is
primarily used in the :cmd:ref:`sim` command.

.. _gtkwave: https://github.com/gtkwave/gtkwave

json11
------

For reading/writing designs from/to JSON, :cmd:ref:`read_json` and
:cmd:ref:`write_json` should be used.  For everything else there is the `json11
library`_:

   json11 is a tiny JSON library for C++11, providing JSON parsing and
   serialization.

This library is used for outputting machine-readable statistics (:cmd:ref:`stat`
with ``-json`` flag), using the RPC frontend (:cmd:ref:`connect_rpc`), and the
yosys-witness ``yw`` format.

.. _json11 library: https://github.com/dropbox/json11

MiniSAT
-------

The files in ``libs/minisat`` provide a high-performance SAT solver, used by the
:cmd:ref:`sat` command.

SHA1
----

The files in ``libs/sha1/`` provide a public domain SHA1 implementation written
by Steve Reid, Bruce Guenter, and Volker Grabsch. It is used for generating
unique names when specializing parameterized modules.

.. _sec:SubCircuit:

SubCircuit
----------

The files in ``libs/subcircuit`` provide a library for solving the subcircuit
isomorphism problem. It is written by C. Wolf and based on the Ullmann Subgraph
Isomorphism Algorithm :cite:p:`UllmannSubgraphIsomorphism`. It is used by the
extract pass (see :doc:`../cmd/extract`).
