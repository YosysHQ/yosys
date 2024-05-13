The extract pass
----------------

- Like the :cmd:ref:`techmap` pass, the :cmd:ref:`extract` pass is called with a
  map file. It compares the circuits inside the modules of the map file with the
  design and looks for sub-circuits in the design that match any of the modules
  in the map file.
- If a match is found, the :cmd:ref:`extract` pass will replace the matching
  subcircuit with an instance of the module from the map file.
- In a way the :cmd:ref:`extract` pass is the inverse of the techmap pass.

.. todo:: add/expand supporting text, also mention custom pattern matching and
   pmgen

Example code can be found in |code_examples/macc|_.

.. |code_examples/macc| replace:: :file:`docs/source/code_examples/macc`
.. _code_examples/macc: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/macc


.. literalinclude:: /code_examples/macc/macc_simple_test.ys
    :language: yoscrypt
    :lines: 1-2

.. figure:: /_images/code_examples/macc/macc_simple_test_00a.*
    :class: width-helper invert-helper
    
    before :cmd:ref:`extract`

.. literalinclude:: /code_examples/macc/macc_simple_test.ys
    :language: yoscrypt
    :lines: 6

.. figure:: /_images/code_examples/macc/macc_simple_test_00b.*
    :class: width-helper invert-helper
    
    after :cmd:ref:`extract`

.. literalinclude:: /code_examples/macc/macc_simple_test.v
   :language: verilog
   :caption: :file:`macc_simple_test.v`

.. literalinclude:: /code_examples/macc/macc_simple_xmap.v
   :language: verilog
   :caption: :file:`macc_simple_xmap.v`

.. literalinclude:: /code_examples/macc/macc_simple_test_01.v
   :language: verilog
   :caption: :file:`macc_simple_test_01.v`

.. figure:: /_images/code_examples/macc/macc_simple_test_01a.*
    :class: width-helper invert-helper

.. figure:: /_images/code_examples/macc/macc_simple_test_01b.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/macc/macc_simple_test_02.v
   :language: verilog
   :caption: :file:`macc_simple_test_02.v`

.. figure:: /_images/code_examples/macc/macc_simple_test_02a.*
    :class: width-helper invert-helper

.. figure:: /_images/code_examples/macc/macc_simple_test_02b.*
    :class: width-helper invert-helper

The wrap-extract-unwrap method
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Often a coarse-grain element has a constant bit-width, but can be used to
implement operations with a smaller bit-width. For example, a 18x25-bit multiplier
can also be used to implement 16x20-bit multiplication.

A way of mapping such elements in coarse grain synthesis is the
wrap-extract-unwrap method:

wrap
  Identify candidate-cells in the circuit and wrap them in a cell with a
  constant wider bit-width using :cmd:ref:`techmap`. The wrappers use the same
  parameters as the original cell, so the information about the original width
  of the ports is preserved. Then use the :cmd:ref:`connwrappers` command to
  connect up the bit-extended in- and outputs of the wrapper cells.

extract
  Now all operations are encoded using the same bit-width as the coarse grain
  element. The :cmd:ref:`extract` command can be used to replace circuits with
  cells of the target architecture.

unwrap
  The remaining wrapper cell can be unwrapped using :cmd:ref:`techmap`.

Example: DSP48_MACC
~~~~~~~~~~~~~~~~~~~

This section details an example that shows how to map MACC operations of
arbitrary size to MACC cells with a 18x25-bit multiplier and a 48-bit adder
(such as the Xilinx DSP48 cells).

Preconditioning: :file:`macc_xilinx_swap_map.v`

Make sure ``A`` is the smaller port on all multipliers

.. todo:: add/expand supporting text

.. literalinclude:: /code_examples/macc/macc_xilinx_swap_map.v
   :language: verilog
   :caption: :file:`macc_xilinx_swap_map.v`

Wrapping multipliers: :file:`macc_xilinx_wrap_map.v`

.. literalinclude:: /code_examples/macc/macc_xilinx_wrap_map.v
   :language: verilog
   :lines: 1-46
   :caption: :file:`macc_xilinx_wrap_map.v`

Wrapping adders: :file:`macc_xilinx_wrap_map.v`

.. literalinclude:: /code_examples/macc/macc_xilinx_wrap_map.v
   :language: verilog
   :lines: 48-89
   :caption: :file:`macc_xilinx_wrap_map.v`

Extract: :file:`macc_xilinx_xmap.v`

.. literalinclude:: /code_examples/macc/macc_xilinx_xmap.v
   :language: verilog
   :caption: :file:`macc_xilinx_xmap.v`

... simply use the same wrapping commands on this module as on the design to
create a template for the :cmd:ref:`extract` command.

Unwrapping multipliers: :file:`macc_xilinx_unwrap_map.v`

.. literalinclude:: /code_examples/macc/macc_xilinx_unwrap_map.v
   :language: verilog
   :lines: 1-30
   :caption: ``$__mul_wrapper`` module in :file:`macc_xilinx_unwrap_map.v`

Unwrapping adders: :file:`macc_xilinx_unwrap_map.v`

.. literalinclude:: /code_examples/macc/macc_xilinx_unwrap_map.v
   :language: verilog
   :lines: 32-61
   :caption: ``$__add_wrapper`` module in :file:`macc_xilinx_unwrap_map.v`

.. literalinclude:: /code_examples/macc/macc_xilinx_test.v
   :language: verilog
   :lines: 1-6
   :caption: ``test1`` of :file:`macc_xilinx_test.v`

.. figure:: /_images/code_examples/macc/macc_xilinx_test1a.*
    :class: width-helper invert-helper

.. figure:: /_images/code_examples/macc/macc_xilinx_test1b.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/macc/macc_xilinx_test.v
   :language: verilog
   :lines: 8-13
   :caption: ``test2`` of :file:`macc_xilinx_test.v`

.. figure:: /_images/code_examples/macc/macc_xilinx_test2a.*
    :class: width-helper invert-helper

.. figure:: /_images/code_examples/macc/macc_xilinx_test2b.*
    :class: width-helper invert-helper

Wrapping in ``test1``:

.. figure:: /_images/code_examples/macc/macc_xilinx_test1b.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/macc/macc_xilinx_test.ys
    :language: yoscrypt
    :start-after: part c
    :end-before: end part c

.. figure:: /_images/code_examples/macc/macc_xilinx_test1c.*
    :class: width-helper invert-helper

Wrapping in ``test2``:

.. figure:: /_images/code_examples/macc/macc_xilinx_test2b.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/macc/macc_xilinx_test.ys
    :language: yoscrypt
    :start-after: part c
    :end-before: end part c

.. figure:: /_images/code_examples/macc/macc_xilinx_test2c.*
    :class: width-helper invert-helper

Extract in ``test1``:

.. figure:: /_images/code_examples/macc/macc_xilinx_test1c.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/macc/macc_xilinx_test.ys
    :language: yoscrypt
    :start-after: part d
    :end-before: end part d

.. figure:: /_images/code_examples/macc/macc_xilinx_test1d.*
    :class: width-helper invert-helper

Extract in ``test2``:

.. figure:: /_images/code_examples/macc/macc_xilinx_test2c.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/macc/macc_xilinx_test.ys
    :language: yoscrypt
    :start-after: part d
    :end-before: end part d

.. figure:: /_images/code_examples/macc/macc_xilinx_test2d.*
    :class: width-helper invert-helper

Unwrap in ``test2``:

.. figure:: /_images/code_examples/macc/macc_xilinx_test2d.*
    :class: width-helper invert-helper

.. literalinclude:: /code_examples/macc/macc_xilinx_test.ys
    :language: yoscrypt
    :start-after: part e
    :end-before: end part e

.. figure:: /_images/code_examples/macc/macc_xilinx_test2e.*
    :class: width-helper invert-helper