Technology mapping 
==================

.. todo:: less academic, check text is coherent

Previous chapters outlined how HDL code is transformed into an RTL netlist. The
RTL netlist is still based on abstract coarse-grain cell types like arbitrary
width adders and even multipliers. This chapter covers how an RTL netlist is
transformed into a functionally equivalent netlist utilizing the cell types
available in the target architecture.

Technology mapping is often performed in two phases. In the first phase RTL
cells are mapped to an internal library of single-bit cells (see
:ref:`sec:celllib_gates`). In the second phase this netlist of internal gate
types is transformed to a netlist of gates from the target technology library.

When the target architecture provides coarse-grain cells (such as block ram or
ALUs), these must be mapped to directly form the RTL netlist, as information on
the coarse-grain structure of the design is lost when it is mapped to bit-width
gate types.

Cell substitution
-----------------

The simplest form of technology mapping is cell substitution, as performed by
the techmap pass. This pass, when provided with a Verilog file that implements
the RTL cell types using simpler cells, simply replaces the RTL cells with the
provided implementation.

When no map file is provided, techmap uses a built-in map file that maps the
Yosys RTL cell types to the internal gate library used by Yosys. The curious
reader may find this map file as `techlibs/common/techmap.v` in the Yosys source
tree.

Additional features have been added to techmap to allow for conditional mapping
of cells (see :doc:`/cmd/techmap`). This can for example be useful if the target
architecture supports hardware multipliers for certain bit-widths but not for
others.

A usual synthesis flow would first use the techmap pass to directly map some RTL
cells to coarse-grain cells provided by the target architecture (if any) and
then use techmap with the built-in default file to map the remaining RTL cells
to gate logic.

Subcircuit substitution
-----------------------

Sometimes the target architecture provides cells that are more powerful than the
RTL cells used by Yosys. For example a cell in the target architecture that can
calculate the absolute-difference of two numbers does not match any single RTL
cell type but only combinations of cells.

For these cases Yosys provides the extract pass that can match a given set of
modules against a design and identify the portions of the design that are
identical (i.e. isomorphic subcircuits) to any of the given modules. These
matched subcircuits are then replaced by instances of the given modules.

The extract pass also finds basic variations of the given modules, such as
swapped inputs on commutative cell types.

In addition to this the extract pass also has limited support for frequent
subcircuit mining, i.e. the process of finding recurring subcircuits in the
design. This has a few applications, including the design of new coarse-grain
architectures :cite:p:`intersynthFdlBookChapter`.

The hard algorithmic work done by the extract pass (solving the isomorphic
subcircuit problem and frequent subcircuit mining) is performed using the
SubCircuit library that can also be used stand-alone without Yosys (see
:ref:`sec:SubCircuit`).

.. _sec:techmap_extern:

Gate-level technology mapping
-----------------------------

.. todo:: newer techmap libraries appear to be largely ``.v`` instead of ``.lib``

On the gate-level the target architecture is usually described by a "Liberty
file". The Liberty file format is an industry standard format that can be used
to describe the behaviour and other properties of standard library cells .

Mapping a design utilizing the Yosys internal gate library (e.g. as a result of
mapping it to this representation using the techmap pass) is performed in two
phases.

First the register cells must be mapped to the registers that are available on
the target architectures. The target architecture might not provide all
variations of d-type flip-flops with positive and negative clock edge,
high-active and low-active asynchronous set and/or reset, etc. Therefore the
process of mapping the registers might add additional inverters to the design
and thus it is important to map the register cells first.

Mapping of the register cells may be performed by using the dfflibmap pass. This
pass expects a Liberty file as argument (using the -liberty option) and only
uses the register cells from the Liberty file.

Secondly the combinational logic must be mapped to the target architecture. This
is done using the external program ABC via the abc pass by using the -liberty
option to the pass. Note that in this case only the combinatorial cells are used
from the cell library.

Occasionally Liberty files contain trade secrets (such as sensitive timing
information) that cannot be shared freely. This complicates processes such as
reporting bugs in the tools involved. When the information in the Liberty file
used by Yosys and ABC are not part of the sensitive information, the additional
tool yosys-filterlib (see :ref:`sec:filterlib`) can be used to strip the
sensitive information from the Liberty file.
