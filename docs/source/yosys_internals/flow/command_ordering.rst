Command ordering
----------------

.. todo:: copypaste

Intro to coarse-grain synthesis
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In coarse-grain synthesis the target architecture has cells of the same
complexity or larger complexity than the internal RTL representation.

For example:

.. code:: verilog

	wire [15:0] a, b;
	wire [31:0] c, y;
	assign y = a * b + c;

This circuit contains two cells in the RTL representation: one multiplier and
one adder. In some architectures this circuit can be implemented using
a single circuit element, for example an FPGA DSP core. Coarse grain synthesis
is this mapping of groups of circuit elements to larger components.

Fine-grain synthesis would be matching the circuit elements to smaller
components, such as LUTs, gates, or half- and full-adders.

The extract pass
~~~~~~~~~~~~~~~~

- Like the :cmd:ref:`techmap` pass, the :cmd:ref:`extract` pass is called with a
  map file. It compares the circuits inside the modules of the map file with the
  design and looks for sub-circuits in the design that match any of the modules
  in the map file.
- If a match is found, the :cmd:ref:`extract` pass will replace the matching
  subcircuit with an instance of the module from the map file.
- In a way the :cmd:ref:`extract` pass is the inverse of the techmap pass.

.. todo:: copypaste

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_simple_test_00a.*
    :class: width-helper
    
    before `extract`

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_simple_test_00b.*
    :class: width-helper
    
    after `extract`

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_simple_test.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_simple_test.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_simple_xmap.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_simple_xmap.v``

.. code:: yoscrypt

    read_verilog macc_simple_test.v
    hierarchy -check -top test

    extract -map macc_simple_xmap.v;;

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_simple_test_01.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_simple_test_01.v``

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_simple_test_01a.*
    :class: width-helper

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_simple_test_01b.*
    :class: width-helper

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_simple_test_02.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_simple_test_02.v``

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_simple_test_02a.*
    :class: width-helper

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_simple_test_02b.*
    :class: width-helper

The wrap-extract-unwrap method
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Often a coarse-grain element has a constant bit-width, but can be used to
implement operations with a smaller bit-width. For example, a 18x25-bit multiplier
can also be used to implement 16x20-bit multiplication.

A way of mapping such elements in coarse grain synthesis is the wrap-extract-unwrap method:

wrap
  Identify candidate-cells in the circuit and wrap them in a cell with a
  constant wider bit-width using :cmd:ref:`techmap`. The wrappers use the same
  parameters as the original cell, so the information about the original width
  of the ports is preserved. Then use the ``connwrappers`` command to connect up
  the bit-extended in- and outputs of the wrapper cells.

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

Preconditioning: ``macc_xilinx_swap_map.v``

Make sure ``A`` is the smaller port on all multipliers

.. todo:: copypaste

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_xilinx_swap_map.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_xilinx_swap_map.v``

Wrapping multipliers: ``macc_xilinx_wrap_map.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_xilinx_wrap_map.v
   :language: verilog
   :lines: 1-46
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_xilinx_wrap_map.v``

Wrapping adders: ``macc_xilinx_wrap_map.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_xilinx_wrap_map.v
   :language: verilog
   :lines: 48-89
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_xilinx_wrap_map.v``

Extract: ``macc_xilinx_xmap.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_xilinx_xmap.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_xilinx_xmap.v``

... simply use the same wrapping commands on this module as on the design to
create a template for the :cmd:ref:`extract` command.

Unwrapping multipliers: ``macc_xilinx_unwrap_map.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_xilinx_unwrap_map.v
   :language: verilog
   :lines: 1-30
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_xilinx_unwrap_map.v``

Unwrapping adders: ``macc_xilinx_unwrap_map.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_xilinx_unwrap_map.v
   :language: verilog
   :lines: 32-61
   :caption: ``docs/resources/PRESENTATION_ExAdv/macc_xilinx_unwrap_map.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_xilinx_test.v
   :language: verilog
   :lines: 1-6
   :caption: ``test1`` of ``docs/resources/PRESENTATION_ExAdv/macc_xilinx_test.v``

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test1a.*
    :class: width-helper

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test1b.*
    :class: width-helper

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/macc_xilinx_test.v
   :language: verilog
   :lines: 8-13
   :caption: ``test2`` of ``docs/resources/PRESENTATION_ExAdv/macc_xilinx_test.v``

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test2a.*
    :class: width-helper

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test2b.*
    :class: width-helper

Wrapping in ``test1``:

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test1b.*
    :class: width-helper

.. code:: yoscrypt

    techmap -map macc_xilinx_wrap_map.v

    connwrappers -unsigned $__mul_wrapper \
                                Y Y_WIDTH \
                -unsigned $__add_wrapper \
                                Y Y_WIDTH ;;

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test1c.*
    :class: width-helper

Wrapping in ``test2``:

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test2b.*
    :class: width-helper

.. code:: yoscrypt

    techmap -map macc_xilinx_wrap_map.v

    connwrappers -unsigned $__mul_wrapper \
                                Y Y_WIDTH \
                 -unsigned $__add_wrapper \
                                Y Y_WIDTH ;;

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test2c.*
    :class: width-helper

Extract in ``test1``:

.. code:: yoscrypt

    design -push
    read_verilog macc_xilinx_xmap.v
    techmap -map macc_xilinx_swap_map.v
    techmap -map macc_xilinx_wrap_map.v;;
    design -save __macc_xilinx_xmap
    design -pop

    extract -constports -ignore_parameters \
            -map %__macc_xilinx_xmap       \
            -swap $__add_wrapper A,B ;;

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test1c.*
    :class: width-helper

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test1d.*
    :class: width-helper

Extract in ``test2``:

.. code:: yoscrypt

    design -push
    read_verilog macc_xilinx_xmap.v
    techmap -map macc_xilinx_swap_map.v
    techmap -map macc_xilinx_wrap_map.v;;
    design -save __macc_xilinx_xmap
    design -pop

    extract -constports -ignore_parameters \
            -map %__macc_xilinx_xmap       \
            -swap $__add_wrapper A,B ;;

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test2c.*
    :class: width-helper

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test2d.*
    :class: width-helper

Unwrap in ``test2``:

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test2d.*
    :class: width-helper

.. figure:: ../../../images/res/PRESENTATION_ExAdv/macc_xilinx_test2e.*
    :class: width-helper

.. code:: yoscrypt

    techmap -map macc_xilinx_unwrap_map.v ;;
