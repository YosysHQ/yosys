Auxiliary libraries
===================

The Yosys source distribution contains some auxiliary libraries that are
compiled into Yosys and can be used in plugins.

.. TODO:: fill out the newer auxiliary libs

BigInt
------

The files in ``libs/bigint/`` provide a library for performing arithmetic with
arbitrary length integers. It is written by Matt McCutchen.

The BigInt library is used for evaluating constant expressions, e.g. using the
ConstEval class provided in kernel/consteval.h.

See also: http://mattmccutchen.net/bigint/

dlfcn-win32
-----------

The files in ``libs/dlfcn-win32`` provide...

ezSAT
-----

The files in ``libs/ezsat`` provide a library for simplifying generating CNF
formulas for SAT solvers. It also contains bindings of MiniSAT. The ezSAT
library is written by C. Wolf. It is used by the sat pass (see
:doc:`../cmd/sat`).

fst
---

The files in ``libs/fst`` provide...

json11
------

The files in ``libs/json11`` provide...

MiniSAT
-------

The files in ``libs/minisat`` provide...

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
