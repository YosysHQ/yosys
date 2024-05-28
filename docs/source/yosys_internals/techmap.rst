Techmap by example
------------------

As a quick recap, the :cmd:ref:`techmap` command replaces cells in the design
with implementations given as Verilog code (called "map files"). It can replace
Yosys' internal cell types (such as ``$or``) as well as user-defined cell types.

- Verilog parameters are used extensively to customize the internal cell types.
- Additional special parameters are used by techmap to communicate meta-data to
  the map files.
- Special wires are used to instruct techmap how to handle a module in the map
  file.
- Generate blocks and recursion are powerful tools for writing map files.

Code examples used in this document are included in the Yosys code base under
|code_examples/techmap|_.

.. |code_examples/techmap| replace:: :file:`docs/source/code_examples/techmap`
.. _code_examples/techmap: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/techmap


Mapping OR3X1
~~~~~~~~~~~~~

.. todo:: add/expand supporting text

.. note::

    This is a simple example for demonstration only.  Techmap shouldn't be used
    to implement basic logic optimization.

.. literalinclude:: /code_examples/techmap/red_or3x1_map.v
   :language: verilog
   :caption: :file:`red_or3x1_map.v`

.. figure:: /_images/code_examples/techmap/red_or3x1.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/techmap/red_or3x1_test.ys
   :language: yoscrypt
   :caption: :file:`red_or3x1_test.ys`

.. literalinclude:: /code_examples/techmap/red_or3x1_test.v
   :language: verilog
   :caption: :file:`red_or3x1_test.v`

Conditional techmap
~~~~~~~~~~~~~~~~~~~

- In some cases only cells with certain properties should be substituted.
- The special wire ``_TECHMAP_FAIL_`` can be used to disable a module in the map
  file for a certain set of parameters.
- The wire ``_TECHMAP_FAIL_`` must be set to a constant value. If it is non-zero
  then the module is disabled for this set of parameters.
- Example use-cases:

    - coarse-grain cell types that only operate on certain bit widths
    - memory resources for different memory geometries (width, depth, ports,
      etc.)

Example:

.. figure:: /_images/code_examples/techmap/sym_mul.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/techmap/sym_mul_map.v
   :language: verilog
   :caption: :file:`sym_mul_map.v`

.. literalinclude:: /code_examples/techmap/sym_mul_test.v
   :language: verilog
   :caption: :file:`sym_mul_test.v`

.. literalinclude:: /code_examples/techmap/sym_mul_test.ys
   :language: yoscrypt
   :caption: :file:`sym_mul_test.ys`


Scripting in map modules
~~~~~~~~~~~~~~~~~~~~~~~~

- The special wires ``_TECHMAP_DO_*`` can be used to run Yosys scripts in the
  context of the replacement module.
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

.. figure:: /_images/code_examples/techmap/mymul.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/techmap/mymul_map.v
   :language: verilog
   :caption: :file:`mymul_map.v`

.. literalinclude:: /code_examples/techmap/mymul_test.v
   :language: verilog
   :caption: :file:`mymul_test.v`

.. literalinclude:: /code_examples/techmap/mymul_test.ys
   :language: yoscrypt
   :caption: :file:`mymul_test.ys`

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

.. figure:: /_images/code_examples/techmap/mulshift.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/techmap/mulshift_map.v
   :language: verilog
   :caption: :file:`mulshift_map.v`

.. literalinclude:: /code_examples/techmap/mulshift_test.v
   :language: verilog
   :caption: :file:`mulshift_test.v`

.. literalinclude:: /code_examples/techmap/mulshift_test.ys
   :language: yoscrypt
   :caption: :file:`mulshift_test.ys`

Handling shorted inputs
~~~~~~~~~~~~~~~~~~~~~~~

- The special parameters ``_TECHMAP_BITS_CONNMAP_`` and
  ``_TECHMAP_CONNMAP_<port-name>_`` can be used to handle shorted inputs.
- Each bit of the port correlates to an ``_TECHMAP_BITS_CONNMAP_`` bits wide
  number in ``_TECHMAP_CONNMAP_<port-name>_``.
- Each unique signal bit is assigned its own number. Identical fields in the
  ``_TECHMAP_CONNMAP_<port-name>_`` parameters mean shorted signal bits.
- The numbers 0-3 are reserved for ``0``, ``1``, ``x``, and ``z`` respectively.
- Example use-cases:

    - Detecting shared clock or control signals in memory interfaces.
    - In some cases this can be used for for optimization.

Example:

.. figure:: /_images/code_examples/techmap/addshift.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/techmap/addshift_map.v
   :language: verilog
   :caption: :file:`addshift_map.v`

.. literalinclude:: /code_examples/techmap/addshift_test.v
   :language: verilog
   :caption: :file:`addshift_test.v`

.. literalinclude:: /code_examples/techmap/addshift_test.ys
   :language: yoscrypt
   :caption: :file:`addshift_test.ys`

Notes on using techmap
~~~~~~~~~~~~~~~~~~~~~~

- Don't use positional cell parameters in map modules.
- You can use the ``$__``-prefix for internal cell types to avoid collisions
  with the user-namespace. But always use two underscores or the internal
  consistency checker will trigger on these cells.
- Techmap has two major use cases:

    - Creating good logic-level representation of arithmetic functions. This
      also means using dedicated hardware resources such as half- and full-adder
      cells in ASICS or dedicated carry logic in FPGAs.
    - Mapping of coarse-grain resources such as block memory or DSP cells.
