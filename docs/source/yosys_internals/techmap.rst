.. _chapter:techmap:

.. todo:: copypaste

Technology mapping 
==================

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

Techmap by example
------------------

.. todo:: copypaste

As a quick recap, the :cmd:ref:`techmap` command replaces cells in the design
with implementations given as Verilog code (called "map files"). It can replace
Yosys' internal cell types (such as ``$or``) as well as user-defined cell types.

- Verilog parameters are used extensively to customize the internal cell types.
- Additional special parameters are used by techmap to communicate meta-data to
  the map files.
- Special wires are used to instruct techmap how to handle a module in the map
  file.
- Generate blocks and recursion are powerful tools for writing map files.

Mapping OR3X1
~~~~~~~~~~~~~

.. note::

    This is a simple example for demonstration only.  Techmap shouldn't be used
    to implement basic logic optimization.

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/red_or3x1_map.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/red_or3x1_map.v``

.. figure:: ../../images/res/PRESENTATION_ExAdv/red_or3x1.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/red_or3x1_test.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExAdv/red_or3x1_test.ys``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/red_or3x1_test.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/red_or3x1_test.v``

Conditional techmap
~~~~~~~~~~~~~~~~~~~

- In some cases only cells with certain properties should be substituted.
- The special wire ``_TECHMAP_FAIL_`` can be used to disable a module
  in the map file for a certain set of parameters.
- The wire ``_TECHMAP_FAIL_`` must be set to a constant value. If it
  is non-zero then the module is disabled for this set of parameters.
- Example use-cases:

    - coarse-grain cell types that only operate on certain bit widths
    - memory resources for different memory geometries (width, depth, ports, etc.)

Example:

.. figure:: ../../images/res/PRESENTATION_ExAdv/sym_mul.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/sym_mul_map.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/sym_mul_map.v``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/sym_mul_test.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/sym_mul_test.v``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/sym_mul_test.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExAdv/sym_mul_test.ys``


Scripting in map modules
~~~~~~~~~~~~~~~~~~~~~~~~

- The special wires ``_TECHMAP_DO_*`` can be used to run Yosys scripts
  in the context of the replacement module.
- The wire that comes first in alphabetical oder is interpreted as string (must
  be connected to constants) that is executed as script. Then the wire is
  removed. Repeat.
- You can even call techmap recursively!
- Example use-cases:

    - Using always blocks in map module: call :cmd:ref:`proc`
    - Perform expensive optimizations (such as :cmd:ref:`freduce`) on cells
      where this is known to work well.
    - Interacting with custom commands.

.. note:: PROTIP:

    Commands such as :cmd:ref:`shell`, ``show -pause``, and :cmd:ref:`dump` can
    be used in the ``_TECHMAP_DO_*`` scripts for debugging map modules.

Example:

.. figure:: ../../images/res/PRESENTATION_ExAdv/mymul.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/mymul_map.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/mymul_map.v``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/mymul_test.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/mymul_test.v``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/mymul_test.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExAdv/mymul_test.ys``

Handling constant inputs
~~~~~~~~~~~~~~~~~~~~~~~~

- The special parameters ``_TECHMAP_CONSTMSK_<port-name>_`` and
  ``_TECHMAP_CONSTVAL_<port-name>_`` can be used to handle constant input values
  to cells.
- The former contains 1-bits for all constant input bits on the port.
- The latter contains the constant bits or undef (x) for non-constant bits.
- Example use-cases:

    - Converting arithmetic (for example multiply to shift).
    - Identify constant addresses or enable bits in memory interfaces.

Example:

.. figure:: ../../images/res/PRESENTATION_ExAdv/mulshift.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/mulshift_map.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/mulshift_map.v``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/mulshift_test.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/mulshift_test.v``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/mulshift_test.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExAdv/mulshift_test.ys``

Handling shorted inputs
~~~~~~~~~~~~~~~~~~~~~~~

- The special parameters ``_TECHMAP_BITS_CONNMAP_`` and
  ``_TECHMAP_CONNMAP_<port-name>_`` can be used to handle shorted inputs.
- Each bit of the port correlates to an ``_TECHMAP_BITS_CONNMAP_`` bits wide
  number in ``_TECHMAP_CONNMAP_<port-name>_``.
- Each unique signal bit is assigned its own number. Identical fields in the ``_TECHMAP_CONNMAP_<port-name>_`` parameters mean shorted signal bits.
- The numbers 0-3 are reserved for ``0``, ``1``, ``x``, and ``z`` respectively.
- Example use-cases:

    - Detecting shared clock or control signals in memory interfaces.
    - In some cases this can be used for for optimization.

Example:

.. figure:: ../../images/res/PRESENTATION_ExAdv/addshift.*
    :class: width-helper

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/addshift_map.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/addshift_map.v``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/addshift_test.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/addshift_test.v``

.. literalinclude:: ../../resources/PRESENTATION_ExAdv/addshift_test.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExAdv/addshift_test.ys``

Notes on using techmap
~~~~~~~~~~~~~~~~~~~~~~

- Don't use positional cell parameters in map modules.
- You can use the ``$__``-prefix for internal cell types to avoid
  collisions with the user-namespace. But always use two underscores or the
  internal consistency checker will trigger on this cells.
- Techmap has two major use cases:

    - Creating good logic-level representation of arithmetic functions. This
      also means using dedicated hardware resources such as half- and full-adder
      cells in ASICS or dedicated carry logic in FPGAs.
    - Mapping of coarse-grain resources such as block memory or DSP cells.
