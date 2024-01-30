.. role:: verilog(code)
	:language: Verilog

.. _chapter:celllib:

Internal cell library
=====================

Most of the passes in Yosys operate on netlists, i.e. they only care about the
RTLIL::Wire and RTLIL::Cell objects in an RTLIL::Module. This chapter discusses
the cell types used by Yosys to represent a behavioural design internally.

This chapter is split in two parts. In the first part the internal RTL cells are
covered. These cells are used to represent the design on a coarse grain level.
Like in the original HDL code on this level the cells operate on vectors of
signals and complex cells like adders exist. In the second part the internal
gate cells are covered. These cells are used to represent the design on a
fine-grain gate-level. All cells from this category operate on single bit
signals.

RTL cells
---------

Most of the RTL cells closely resemble the operators available in HDLs such as
Verilog or VHDL. Therefore Verilog operators are used in the following sections
to define the behaviour of the RTL cells.

Note that all RTL cells have parameters indicating the size of inputs and
outputs. When passes modify RTL cells they must always keep the values of these
parameters in sync with the size of the signals connected to the inputs and
outputs.

Simulation models for the RTL cells can be found in the file
``techlibs/common/simlib.v`` in the Yosys source tree.

Unary operators
~~~~~~~~~~~~~~~

All unary RTL cells have one input port ``\A`` and one output port ``\Y``. They
also have the following parameters:

``\A_SIGNED``
	Set to a non-zero value if the input ``\A`` is signed and therefore
	should be sign-extended when needed.

``\A_WIDTH``
	The width of the input port ``\A``.

``\Y_WIDTH``
	The width of the output port ``\Y``.

:numref:`tab:CellLib_unary` lists all cells for unary RTL operators.

.. table:: Cell types for unary operators with their corresponding Verilog expressions.
	:name: tab:CellLib_unary

	================== ============
	Verilog            Cell Type
	================== ============
	:verilog:`Y =  ~A` $not
	:verilog:`Y =  +A` $pos
	:verilog:`Y =  -A` $neg
	:verilog:`Y =  &A` $reduce_and
	:verilog:`Y =  |A` $reduce_or
	:verilog:`Y =  ^A` $reduce_xor
	:verilog:`Y = ~^A` $reduce_xnor
	:verilog:`Y =  |A` $reduce_bool
	:verilog:`Y =  !A` $logic_not
	================== ============

For the unary cells that output a logical value (``$reduce_and``,
``$reduce_or``, ``$reduce_xor``, ``$reduce_xnor``, ``$reduce_bool``,
``$logic_not``), when the ``\Y_WIDTH`` parameter is greater than 1, the output
is zero-extended, and only the least significant bit varies.

Note that ``$reduce_or`` and ``$reduce_bool`` actually represent the same logic
function. But the HDL frontends generate them in different situations. A
``$reduce_or`` cell is generated when the prefix ``|`` operator is being used. A
``$reduce_bool`` cell is generated when a bit vector is used as a condition in
an ``if``-statement or ``?:``-expression.

Binary operators
~~~~~~~~~~~~~~~~

All binary RTL cells have two input ports ``\A`` and ``\B`` and one output port
``\Y``. They also have the following parameters:

``\A_SIGNED``
	Set to a non-zero value if the input ``\A`` is signed and therefore
	should be sign-extended when needed.

``\A_WIDTH``
	The width of the input port ``\A``.

``\B_SIGNED``
	Set to a non-zero value if the input ``\B`` is signed and therefore
	should be sign-extended when needed.

``\B_WIDTH``
	The width of the input port ``\B``.

``\Y_WIDTH``
	The width of the output port ``\Y``.

:numref:`tab:CellLib_binary` lists all cells for binary RTL operators.

.. table:: Cell types for binary operators with their corresponding Verilog expressions.
	:name: tab:CellLib_binary

	======================= ============= ======================= =========
	Verilog 	        Cell Type     Verilog                 Cell Type
	======================= ============= ======================= =========
	:verilog:`Y = A  & B`   $and          :verilog:`Y = A <  B`   $lt
	:verilog:`Y = A  | B`   $or           :verilog:`Y = A <= B`   $le
	:verilog:`Y = A  ^ B`   $xor          :verilog:`Y = A == B`   $eq
	:verilog:`Y = A ~^ B`   $xnor         :verilog:`Y = A != B`   $ne
	:verilog:`Y = A << B`   $shl          :verilog:`Y = A >= B`   $ge
	:verilog:`Y = A >> B`   $shr          :verilog:`Y = A >  B`   $gt
	:verilog:`Y = A <<< B`  $sshl         :verilog:`Y = A  + B`   $add
	:verilog:`Y = A >>> B`  $sshr         :verilog:`Y = A  - B`   $sub
	:verilog:`Y = A && B`   $logic_and    :verilog:`Y = A  * B`   $mul
	:verilog:`Y = A || B`   $logic_or     :verilog:`Y = A  / B`   $div
	:verilog:`Y = A === B`  $eqx          :verilog:`Y = A  % B`   $mod
	:verilog:`Y = A !== B`  $nex          ``N/A``                 $divfloor
	:verilog:`Y = A ** B`   $pow          ``N/A``                 $modfoor
	======================= ============= ======================= =========

The ``$shl`` and ``$shr`` cells implement logical shifts, whereas the ``$sshl``
and ``$sshr`` cells implement arithmetic shifts. The ``$shl`` and ``$sshl``
cells implement the same operation. All four of these cells interpret the second
operand as unsigned, and require ``\B_SIGNED`` to be zero.

Two additional shift operator cells are available that do not directly
correspond to any operator in Verilog, ``$shift`` and ``$shiftx``. The
``$shift`` cell performs a right logical shift if the second operand is positive
(or unsigned), and a left logical shift if it is negative. The ``$shiftx`` cell
performs the same operation as the ``$shift`` cell, but the vacated bit
positions are filled with undef (x) bits, and corresponds to the Verilog indexed
part-select expression.

For the binary cells that output a logical value (``$logic_and``, ``$logic_or``,
``$eqx``, ``$nex``, ``$lt``, ``$le``, ``$eq``, ``$ne``, ``$ge``, ``$gt)``, when
the ``\Y_WIDTH`` parameter is greater than 1, the output is zero-extended, and
only the least significant bit varies.

Division and modulo cells are available in two rounding modes. The original
``$div`` and ``$mod`` cells are based on truncating division, and correspond to
the semantics of the verilog ``/`` and ``%`` operators. The ``$divfloor`` and
``$modfloor`` cells represent flooring division and flooring modulo, the latter
of which is also known as "remainder" in several languages. See
:numref:`tab:CellLib_divmod` for a side-by-side comparison between the different
semantics.

.. table:: Comparison between different rounding modes for division and modulo cells.
	:name: tab:CellLib_divmod

	+-----------+--------+-----------+-----------+-----------+-----------+
	| Division  | Result |      Truncating       |        Flooring       |
	+-----------+--------+-----------+-----------+-----------+-----------+
	|           |        | $div      | $mod      | $divfloor | $modfloor |
	+===========+========+===========+===========+===========+===========+
	| -10 / 3   | -3.3   | -3        |        -1 | -4        |  2        |
	+-----------+--------+-----------+-----------+-----------+-----------+
	| 10 / -3   | -3.3   | -3        |         1 | -4        | -2        |
	+-----------+--------+-----------+-----------+-----------+-----------+
	| -10 / -3  |  3.3   |  3        |        -1 |  3        | -1        |
	+-----------+--------+-----------+-----------+-----------+-----------+
	| 10 / 3    |  3.3   |  3        |         1 |  3        |  1        |
	+-----------+--------+-----------+-----------+-----------+-----------+

Multiplexers
~~~~~~~~~~~~

Multiplexers are generated by the Verilog HDL frontend for ``?:``-expressions.
Multiplexers are also generated by the proc pass to map the decision trees from
RTLIL::Process objects to logic.

The simplest multiplexer cell type is ``$mux``. Cells of this type have a
``\WITDH`` parameter and data inputs ``\A`` and ``\B`` and a data output ``\Y``,
all of the specified width. This cell also has a single bit control input
``\S``. If ``\S`` is 0 the value from the input ``\A`` is sent to the output, if
it is 1 the value from the ``\B`` input is sent to the output. So the ``$mux``
cell implements the function :verilog:`Y = S ? B : A`.

The ``$pmux`` cell is used to multiplex between many inputs using a one-hot
select signal. Cells of this type have a ``\WIDTH`` and a ``\S_WIDTH`` parameter
and inputs ``\A``, ``\B``, and ``\S`` and an output ``\Y``. The ``\S`` input is
``\S_WIDTH`` bits wide. The ``\A`` input and the output are both ``\WIDTH`` bits
wide and the ``\B`` input is ``\WIDTH*\S_WIDTH`` bits wide. When all bits of
``\S`` are zero, the value from ``\A`` input is sent to the output. If the
:math:`n`\ 'th bit from ``\S`` is set, the value :math:`n`\ 'th ``\WIDTH`` bits
wide slice of the ``\B`` input is sent to the output. When more than one bit
from ``\S`` is set the output is undefined. Cells of this type are used to model
"parallel cases" (defined by using the ``parallel_case`` attribute or detected
by an optimization).

The ``$tribuf`` cell is used to implement tristate logic. Cells of this type
have a ``\B`` parameter and inputs ``\A`` and ``\EN`` and an output ``\Y``. The
``\A`` input and ``\Y`` output are ``\WIDTH`` bits wide, and the ``\EN`` input
is one bit wide. When ``\EN`` is 0, the output is not driven. When ``\EN`` is 1,
the value from ``\A`` input is sent to the ``\Y`` output. Therefore, the
``$tribuf`` cell implements the function :verilog:`Y = EN ? A : 'bz`.

Behavioural code with cascaded if-then-else- and case-statements usually results
in trees of multiplexer cells. Many passes (from various optimizations to FSM
extraction) heavily depend on these multiplexer trees to understand dependencies
between signals. Therefore optimizations should not break these multiplexer
trees (e.g. by replacing a multiplexer between a calculated signal and a
constant zero with an ``$and`` gate).

Registers
~~~~~~~~~

SR-type latches are represented by ``$sr`` cells. These cells have input ports
``\SET`` and ``\CLR`` and an output port ``\Q``. They have the following
parameters:

``\WIDTH``
	The width of inputs ``\SET`` and ``\CLR`` and output ``\Q``.

``\SET_POLARITY``
	The set input bits are active-high if this parameter has the value
	``1'b1`` and active-low if this parameter is ``1'b0``.

``\CLR_POLARITY``
	The reset input bits are active-high if this parameter has the value
	``1'b1`` and active-low if this parameter is ``1'b0``.

Both set and reset inputs have separate bits for every output bit. When both the
set and reset inputs of an ``$sr`` cell are active for a given bit index, the
reset input takes precedence.

D-type flip-flops are represented by ``$dff`` cells. These cells have a clock
port ``\CLK``, an input port ``\D`` and an output port ``\Q``. The following
parameters are available for ``$dff`` cells:

``\WIDTH``
	The width of input ``\D`` and output ``\Q``.

``\CLK_POLARITY``
	Clock is active on the positive edge if this parameter has the value
	``1'b1`` and on the negative edge if this parameter is ``1'b0``.

D-type flip-flops with asynchronous reset are represented by ``$adff`` cells. As
the ``$dff`` cells they have ``\CLK``, ``\D`` and ``\Q`` ports. In addition they
also have a single-bit ``\ARST`` input port for the reset pin and the following
additional two parameters:

``\ARST_POLARITY``
	The asynchronous reset is active-high if this parameter has the value
	``1'b1`` and active-low if this parameter is ``1'b0``.

``\ARST_VALUE``
   	The state of ``\Q`` will be set to this value when the reset is active.

Usually these cells are generated by the ``proc`` pass using the information in
the designs RTLIL::Process objects.

D-type flip-flops with synchronous reset are represented by ``$sdff`` cells. As
the ``$dff`` cells they have ``\CLK``, ``\D`` and ``\Q`` ports. In addition they
also have a single-bit ``\SRST`` input port for the reset pin and the following
additional two parameters:

``\SRST_POLARITY``
	The synchronous reset is active-high if this parameter has the value
	``1'b1`` and active-low if this parameter is ``1'b0``.

``\SRST_VALUE``
	The state of ``\Q`` will be set to this value when the reset is active.

Note that the ``$adff`` and ``$sdff`` cells can only be used when the reset value is
constant.

D-type flip-flops with asynchronous load are represented by ``$aldff`` cells. As
the ``$dff`` cells they have ``\CLK``, ``\D`` and ``\Q`` ports. In addition they
also have a single-bit ``\ALOAD`` input port for the async load enable pin, a
``\AD`` input port with the same width as data for the async load data, and the
following additional parameter:

``\ALOAD_POLARITY``
	The asynchronous load is active-high if this parameter has the value
	``1'b1`` and active-low if this parameter is ``1'b0``.

D-type flip-flops with asynchronous set and reset are represented by ``$dffsr``
cells. As the ``$dff`` cells they have ``\CLK``, ``\D`` and ``\Q`` ports. In
addition they also have multi-bit ``\SET`` and ``\CLR`` input ports and the
corresponding polarity parameters, like ``$sr`` cells.

D-type flip-flops with enable are represented by ``$dffe``, ``$adffe``,
``$aldffe``, ``$dffsre``, ``$sdffe``, and ``$sdffce`` cells, which are enhanced
variants of ``$dff``, ``$adff``, ``$aldff``, ``$dffsr``, ``$sdff`` (with reset
over enable) and ``$sdff`` (with enable over reset) cells, respectively.  They
have the same ports and parameters as their base cell. In addition they also
have a single-bit ``\EN`` input port for the enable pin and the following
parameter:

``\EN_POLARITY``
	The enable input is active-high if this parameter has the value ``1'b1``
	and active-low if this parameter is ``1'b0``.

D-type latches are represented by ``$dlatch`` cells.  These cells have an enable
port ``\EN``, an input port ``\D``, and an output port ``\Q``.  The following
parameters are available for ``$dlatch`` cells:

``\WIDTH``
	The width of input ``\D`` and output ``\Q``.

``\EN_POLARITY``
	The enable input is active-high if this parameter has the value ``1'b1``
	and active-low if this parameter is ``1'b0``.

The latch is transparent when the ``\EN`` input is active.

D-type latches with reset are represented by ``$adlatch`` cells.  In addition to
``$dlatch`` ports and parameters, they also have a single-bit ``\ARST`` input
port for the reset pin and the following additional parameters:

``\ARST_POLARITY``
	The asynchronous reset is active-high if this parameter has the value
	``1'b1`` and active-low if this parameter is ``1'b0``.

``\ARST_VALUE``
	The state of ``\Q`` will be set to this value when the reset is active.

D-type latches with set and reset are represented by ``$dlatchsr`` cells. In
addition to ``$dlatch`` ports and parameters, they also have multi-bit ``\SET``
and ``\CLR`` input ports and the corresponding polarity parameters, like ``$sr``
cells.

.. _sec:memcells:

Memories
~~~~~~~~

Memories are either represented using RTLIL::Memory objects, ``$memrd_v2``,
``$memwr_v2``, and ``$meminit_v2`` cells, or by ``$mem_v2`` cells alone.

In the first alternative the RTLIL::Memory objects hold the general metadata for
the memory (bit width, size in number of words, etc.) and for each port a
``$memrd_v2`` (read port) or ``$memwr_v2`` (write port) cell is created. Having
individual cells for read and write ports has the advantage that they can be
consolidated using resource sharing passes. In some cases this drastically
reduces the number of required ports on the memory cell. In this alternative,
memory initialization data is represented by ``$meminit_v2`` cells, which allow
delaying constant folding for initialization addresses and data until after the
frontend finishes.

The ``$memrd_v2`` cells have a clock input ``\CLK``, an enable input ``\EN``, an
address input ``\ADDR``, a data output ``\DATA``, an asynchronous reset input
``\ARST``, and a synchronous reset input ``\SRST``. They also have the following
parameters:

``\MEMID``
	The name of the RTLIL::Memory object that is associated with this read
	port.

``\ABITS``
	The number of address bits (width of the ``\ADDR`` input port).

``\WIDTH``
	The number of data bits (width of the ``\DATA`` output port).  Note that
	this may be a power-of-two multiple of the underlying memory's width --
	such ports are called wide ports and access an aligned group of cells at
	once.  In this case, the corresponding low bits of ``\ADDR`` must be
	tied to 0.

``\CLK_ENABLE``
	When this parameter is non-zero, the clock is used. Otherwise this read
	port is asynchronous and the ``\CLK`` input is not used.

``\CLK_POLARITY``
	Clock is active on the positive edge if this parameter has the value
	``1'b1`` and on the negative edge if this parameter is ``1'b0``.

``\TRANSPARENCY_MASK``
	This parameter is a bitmask of write ports that this read port is
	transparent with. The bits of this parameter are indexed by the write
	port's ``\PORTID`` parameter. Transparency can only be enabled between
	synchronous ports sharing a clock domain. When transparency is enabled
	for a given port pair, a read and write to the same address in the same
	cycle will return the new value. Otherwise the old value is returned.

``\COLLISION_X_MASK``
	This parameter is a bitmask of write ports that have undefined collision
	behavior with this port. The bits of this parameter are indexed by the
	write port's ``\PORTID`` parameter. This behavior can only be enabled
	between synchronous ports sharing a clock domain. When undefined
	collision is enabled for a given port pair, a read and write to the same
	address in the same cycle will return the undefined (all-X) value.This
	option is exclusive (for a given port pair) with the transparency
	option.

``\ARST_VALUE``
	Whenever the ``\ARST`` input is asserted, the data output will be reset
	to this value. Only used for synchronous ports.

``\SRST_VALUE``
	Whenever the ``\SRST`` input is synchronously asserted, the data output
	will be reset to this value. Only used for synchronous ports.

``\INIT_VALUE``
	The initial value of the data output, for synchronous ports.

``\CE_OVER_SRST``
	If this parameter is non-zero, the ``\SRST`` input is only recognized
	when ``\EN`` is true. Otherwise, ``\SRST`` is recognized regardless of
	``\EN``.

The ``$memwr_v2`` cells have a clock input ``\CLK``, an enable input ``\EN``
(one enable bit for each data bit), an address input ``\ADDR`` and a data input
``\DATA``. They also have the following parameters:

``\MEMID``
	The name of the RTLIL::Memory object that is associated with this write
	port.

``\ABITS``
	The number of address bits (width of the ``\ADDR`` input port).

``\WIDTH``
	The number of data bits (width of the ``\DATA`` output port). Like with
	``$memrd_v2`` cells, the width is allowed to be any power-of-two
	multiple of memory width, with the corresponding restriction on address.

``\CLK_ENABLE``
	When this parameter is non-zero, the clock is used. Otherwise this write
	port is asynchronous and the ``\CLK`` input is not used.

``\CLK_POLARITY``
	Clock is active on positive edge if this parameter has the value
	``1'b1`` and on the negative edge if this parameter is ``1'b0``.

``\PORTID``
	An identifier for this write port, used to index write port bit mask parameters.

``\PRIORITY_MASK``
	This parameter is a bitmask of write ports that this write port has
	priority over in case of writing to the same address.  The bits of this
	parameter are indexed by the other write port's ``\PORTID`` parameter.
	Write ports can only have priority over write ports with lower port ID.
	When two ports write to the same address and neither has priority over
	the other, the result is undefined.  Priority can only be set between
	two synchronous ports sharing the same clock domain.

The ``$meminit_v2`` cells have an address input ``\ADDR``, a data input
``\DATA``, with the width of the ``\DATA`` port equal to ``\WIDTH`` parameter
times ``\WORDS`` parameter, and a bit enable mask input ``\EN`` with width equal
to ``\WIDTH`` parameter. All three of the inputs must resolve to a constant for
synthesis to succeed.

``\MEMID``
	The name of the RTLIL::Memory object that is associated with this
	initialization cell.

``\ABITS``
	The number of address bits (width of the ``\ADDR`` input port).

``\WIDTH``
	The number of data bits per memory location.

``\WORDS``
	The number of consecutive memory locations initialized by this cell.

``\PRIORITY``
	The cell with the higher integer value in this parameter wins an
	initialization conflict.

The HDL frontend models a memory using RTLIL::Memory objects and asynchronous
``$memrd_v2`` and ``$memwr_v2`` cells. The ``memory`` pass (i.e.~its various
sub-passes) migrates ``$dff`` cells into the ``$memrd_v2`` and ``$memwr_v2``
cells making them synchronous, then converts them to a single ``$mem_v2`` cell
and (optionally) maps this cell type to ``$dff`` cells for the individual words
and multiplexer-based address decoders for the read and write interfaces. When
the last step is disabled or not possible, a ``$mem_v2`` cell is left in the
design.

The ``$mem_v2`` cell provides the following parameters:

``\MEMID``
	The name of the original RTLIL::Memory object that became this
	``$mem_v2`` cell.

``\SIZE``
	The number of words in the memory.

``\ABITS``
	The number of address bits.

``\WIDTH``
	The number of data bits per word.

``\INIT``
	The initial memory contents.

``\RD_PORTS``
	The number of read ports on this memory cell.

``\RD_WIDE_CONTINUATION``
	This parameter is ``\RD_PORTS`` bits wide, containing a bitmask of
	"wide continuation" read ports. Such ports are used to represent the
	extra data bits of wide ports in the combined cell, and must have all
	control signals identical with the preceding port, except for address,
	which must have the proper sub-cell address encoded in the low bits.

``\RD_CLK_ENABLE``
	This parameter is ``\RD_PORTS`` bits wide, containing a clock enable bit
	for each read port.

``\RD_CLK_POLARITY``
	This parameter is ``\RD_PORTS`` bits wide, containing a clock polarity
	bit for each read port.

``\RD_TRANSPARENCY_MASK``
	This parameter is ``\RD_PORTS*\WR_PORTS`` bits wide, containing a
	concatenation of all ``\TRANSPARENCY_MASK`` values of the original
	``$memrd_v2`` cells.

``\RD_COLLISION_X_MASK``
	This parameter is ``\RD_PORTS*\WR_PORTS`` bits wide, containing a
	concatenation of all ``\COLLISION_X_MASK`` values of the original
	``$memrd_v2`` cells.

``\RD_CE_OVER_SRST``
	This parameter is ``\RD_PORTS`` bits wide, determining relative
	synchronous reset and enable priority for each read port.

``\RD_INIT_VALUE``
	This parameter is ``\RD_PORTS*\WIDTH`` bits wide, containing the initial
	value for each synchronous read port.

``\RD_ARST_VALUE``
	This parameter is ``\RD_PORTS*\WIDTH`` bits wide, containing the
	asynchronous reset value for each synchronous read port.

``\RD_SRST_VALUE``
	This parameter is ``\RD_PORTS*\WIDTH`` bits wide, containing the
	synchronous reset value for each synchronous read port.

``\WR_PORTS``
	The number of write ports on this memory cell.

``\WR_WIDE_CONTINUATION``
	This parameter is ``\WR_PORTS`` bits wide, containing a bitmask of
	"wide continuation" write ports.

``\WR_CLK_ENABLE``
	This parameter is ``\WR_PORTS`` bits wide, containing a clock enable bit
	for each write port.

``\WR_CLK_POLARITY``
	This parameter is ``\WR_PORTS`` bits wide, containing a clock polarity
	bit for each write port.

``\WR_PRIORITY_MASK``
	This parameter is ``\WR_PORTS*\WR_PORTS`` bits wide, containing a
	concatenation of all ``\PRIORITY_MASK`` values of the original
	``$memwr_v2`` cells.

The ``$mem_v2`` cell has the following ports:

``\RD_CLK``
	This input is ``\RD_PORTS`` bits wide, containing all clock signals for
	the read ports.

``\RD_EN``
	This input is ``\RD_PORTS`` bits wide, containing all enable signals for
	the read ports.

``\RD_ADDR``
	This input is ``\RD_PORTS*\ABITS`` bits wide, containing all address
	signals for the read ports.

``\RD_DATA``
	This output is ``\RD_PORTS*\WIDTH`` bits wide, containing all data
	signals for the read ports.

``\RD_ARST``
	This input is ``\RD_PORTS`` bits wide, containing all asynchronous reset
	signals for the read ports.

``\RD_SRST``
	This input is ``\RD_PORTS`` bits wide, containing all synchronous reset
	signals for the read ports.

``\WR_CLK``
	This input is ``\WR_PORTS`` bits wide, containing all clock signals for
	the write ports.

``\WR_EN``
	This input is ``\WR_PORTS*\WIDTH`` bits wide, containing all enable
	signals for the write ports.

``\WR_ADDR``
	This input is ``\WR_PORTS*\ABITS`` bits wide, containing all address
	signals for the write ports.

``\WR_DATA``
	This input is ``\WR_PORTS*\WIDTH`` bits wide, containing all data
	signals for the write ports.

The ``memory_collect`` pass can be used to convert discrete ``$memrd_v2``,
``$memwr_v2``, and ``$meminit_v2`` cells belonging to the same memory to a
single ``$mem_v2`` cell, whereas the ``memory_unpack`` pass performs the inverse
operation. The ``memory_dff`` pass can combine asynchronous memory ports that
are fed by or feeding registers into synchronous memory ports. The
``memory_bram`` pass can be used to recognize ``$mem_v2`` cells that can be
implemented with a block RAM resource on an FPGA. The ``memory_map`` pass can be
used to implement ``$mem_v2`` cells as basic logic: word-wide DFFs and address
decoders.

Finite state machines
~~~~~~~~~~~~~~~~~~~~~

Add a brief description of the ``$fsm`` cell type.

Specify rules
~~~~~~~~~~~~~

Add information about ``$specify2``, ``$specify3``, and ``$specrule`` cells.

Formal verification cells
~~~~~~~~~~~~~~~~~~~~~~~~~

Add information about ``$assert``, ``$assume``, ``$live``, ``$fair``,
``$cover``, ``$equiv``, ``$initstate``, ``$anyconst``, ``$anyseq``,
``$anyinit``, ``$allconst``, ``$allseq`` cells.

Add information about ``$ff`` and ``$_FF_`` cells.

Debugging cells
~~~~~~~~~~~~~~~

The ``$print`` cell is used to log the values of signals, akin to (and
translatable to) the ``$display`` and ``$write`` family of tasks in Verilog.  It
has the following parameters:

``\FORMAT``
	The internal format string.  The syntax is described below.

``\ARGS_WIDTH``
	The width (in bits) of the signal on the ``\ARGS`` port.

``\TRG_ENABLE``
	True if triggered on specific signals defined in ``\TRG``; false if
	triggered whenever ``\ARGS`` or ``\EN`` change and ``\EN`` is 1.

If ``\TRG_ENABLE`` is true, the following parameters also apply:

``\TRG_WIDTH``
	The number of bits in the ``\TRG`` port.

``\TRG_POLARITY``
	For each bit in ``\TRG``, 1 if that signal is positive-edge triggered, 0 if
	negative-edge triggered.

``\PRIORITY``
	When multiple ``$print`` cells fire on the same trigger, they execute in
	descending priority order.

Ports:

``\TRG``
	The signals that control when this ``$print`` cell is triggered.
	If the width of this port is zero and ``\TRG_ENABLE`` is true, the cell is
	triggered during initial evaluation (time zero) only.

``\EN``
	Enable signal for the whole cell.

``\ARGS``
	The values to be displayed, in format string order.

Format string syntax
^^^^^^^^^^^^^^^^^^^^

The format string syntax resembles Python f-strings.  Regular text is passed
through unchanged until a format specifier is reached, starting with a ``{``.

Format specifiers have the following syntax.  Unless noted, all items are
required:

``{``
	Denotes the start of the format specifier.

size
	Signal size in bits; this many bits are consumed from the ``\ARGS`` port by
	this specifier.

``:``
	Separates the size from the remaining items.

justify
	``>`` for right-justified, ``<`` for left-justified.

padding
	``0`` for zero-padding, or a space for space-padding.

width\ *?*
	(optional) The number of characters wide to pad to.

base
	* ``b`` for base-2 integers (binary)
	* ``o`` for base-8 integers	(octal)
	* ``d`` for base-10 integers (decimal)
	* ``h`` for base-16	integers (hexadecimal)
	* ``c`` for ASCII characters/strings
	* ``t`` and ``r`` for simulation time (corresponding to :verilog:`$time` and :verilog:`$realtime`)

For integers, this item may follow:

``+``\ *?*
	(optional, decimals only) Include a leading plus for non-negative numbers.
	This can assist with symmetry with negatives in tabulated output.

signedness
	``u`` for unsigned, ``s`` for signed.  This distinction is only respected
	when rendering decimals.

ASCII characters/strings have no special options, but the signal size must be
divisible by 8.

For simulation time, the signal size must be zero.

Finally:

``}``
	Denotes the end of the format specifier.

Some example format specifiers:

+ ``{8:>02hu}`` - 8-bit unsigned integer rendered as hexadecimal,
  right-justified, zero-padded to 2 characters wide.
+ ``{32:< 15d+s}`` - 32-bit signed integer rendered as decimal, left-justified,
  space-padded to 15 characters wide, positive values prefixed with ``+``.
+ ``{16:< 10hu}`` - 16-bit unsigned integer rendered as hexadecimal,
  left-justified, space-padded to 10 characters wide.
+ ``{0:>010t}`` - simulation time, right-justified, zero-padded to 10 characters
  wide.

To include literal ``{`` and ``}`` characters in your format string, use ``{{``
and ``}}`` respectively.

It is an error for a format string to consume more or less bits from ``\ARGS``
than the port width.

Values are never truncated, regardless of the specified width.

Note that further restrictions on allowable combinations of options may apply
depending on the backend used.

For example, Verilog does not have a format specifier that allows zero-padding a
string (i.e. more than 1 ASCII character), though zero-padding a single
character is permitted.

Thus, while the RTLIL format specifier ``{8:>02c}`` translates to ``%02c``,
``{16:>02c}`` cannot be represented in Verilog and will fail to emit.  In this
case, ``{16:> 02c}`` must be used, which translates to ``%2s``.

.. _sec:celllib_gates:

Gates
-----

For gate level logic networks, fixed function single bit cells are used that do
not provide any parameters.

Simulation models for these cells can be found in the file
techlibs/common/simcells.v in the Yosys source tree.

.. table:: Cell types for gate level logic networks (main list)
	:name: tab:CellLib_gates

	======================================= ============
	Verilog                                 Cell Type
	======================================= ============
	:verilog:`Y = A`                        $_BUF_
	:verilog:`Y = ~A`                       $_NOT_
	:verilog:`Y = A & B`                    $_AND_
	:verilog:`Y = ~(A & B)`                 $_NAND_
	:verilog:`Y = A & ~B`                   $_ANDNOT_
	:verilog:`Y = A | B`                    $_OR_
	:verilog:`Y = ~(A | B)`                 $_NOR_
	:verilog:`Y = A | ~B`                   $_ORNOT_
	:verilog:`Y = A ^ B`                    $_XOR_
	:verilog:`Y = ~(A ^ B)`                 $_XNOR_
	:verilog:`Y = ~((A & B) | C)`           $_AOI3_
	:verilog:`Y = ~((A | B) & C)`           $_OAI3_
	:verilog:`Y = ~((A & B) | (C & D))`     $_AOI4_
	:verilog:`Y = ~((A | B) & (C | D))`     $_OAI4_
	:verilog:`Y = S ? B : A`                $_MUX_
	:verilog:`Y = ~(S ? B : A)`             $_NMUX_
	(see below)                             $_MUX4_
	(see below)                             $_MUX8_
	(see below)                             $_MUX16_
	:verilog:`Y = EN ? A : 1'bz`            $_TBUF_
	:verilog:`always @(negedge C) Q <= D`   $_DFF_N_
	:verilog:`always @(posedge C) Q <= D`   $_DFF_P_
	:verilog:`always @* if (!E) Q <= D`     $_DLATCH_N_
	:verilog:`always @* if (E)  Q <= D`     $_DLATCH_P_
	======================================= ============

.. table:: Cell types for gate level logic networks (FFs with reset)
	:name: tab:CellLib_gates_adff

	================== ============== ============== =======================
	:math:`ClkEdge`    :math:`RstLvl` :math:`RstVal` Cell Type
	================== ============== ============== =======================
	:verilog:`negedge` ``0``          ``0``          $_DFF_NN0_, $_SDFF_NN0_
	:verilog:`negedge` ``0``          ``1``          $_DFF_NN1_, $_SDFF_NN1_
	:verilog:`negedge` ``1``          ``0``          $_DFF_NP0_, $_SDFF_NP0_
	:verilog:`negedge` ``1``          ``1``          $_DFF_NP1_, $_SDFF_NP1_
	:verilog:`posedge` ``0``          ``0``          $_DFF_PN0_, $_SDFF_PN0_
	:verilog:`posedge` ``0``          ``1``          $_DFF_PN1_, $_SDFF_PN1_
	:verilog:`posedge` ``1``          ``0``          $_DFF_PP0_, $_SDFF_PP0_
	:verilog:`posedge` ``1``          ``1``          $_DFF_PP1_, $_SDFF_PP1_
	================== ============== ============== =======================


.. table:: Cell types for gate level logic networks (FFs with enable)
	:name: tab:CellLib_gates_dffe

	================== ============= ===========
	:math:`ClkEdge`    :math:`EnLvl` Cell Type
	================== ============= ===========
	:verilog:`negedge` ``0``         $_DFFE_NN_
	:verilog:`negedge` ``1``         $_DFFE_NP_
	:verilog:`posedge` ``0``         $_DFFE_PN_
	:verilog:`posedge` ``1``         $_DFFE_PP_
	================== ============= ===========


.. table:: Cell types for gate level logic networks (FFs with reset and enable)
	:name: tab:CellLib_gates_adffe

	================== ============== ============== ============= ===========================================
	:math:`ClkEdge`    :math:`RstLvl` :math:`RstVal` :math:`EnLvl` Cell Type
	================== ============== ============== ============= ===========================================
	:verilog:`negedge` ``0``          ``0``          ``0``         $_DFFE_NN0N_, $_SDFFE_NN0N_, $_SDFFCE_NN0N_
	:verilog:`negedge` ``0``          ``0``          ``1``         $_DFFE_NN0P_, $_SDFFE_NN0P_, $_SDFFCE_NN0P_
	:verilog:`negedge` ``0``          ``1``          ``0``         $_DFFE_NN1N_, $_SDFFE_NN1N_, $_SDFFCE_NN1N_
	:verilog:`negedge` ``0``          ``1``          ``1``         $_DFFE_NN1P_, $_SDFFE_NN1P_, $_SDFFCE_NN1P_
	:verilog:`negedge` ``1``          ``0``          ``0``         $_DFFE_NP0N_, $_SDFFE_NP0N_, $_SDFFCE_NP0N_
	:verilog:`negedge` ``1``          ``0``          ``1``         $_DFFE_NP0P_, $_SDFFE_NP0P_, $_SDFFCE_NP0P_
	:verilog:`negedge` ``1``          ``1``          ``0``         $_DFFE_NP1N_, $_SDFFE_NP1N_, $_SDFFCE_NP1N_
	:verilog:`negedge` ``1``          ``1``          ``1``         $_DFFE_NP1P_, $_SDFFE_NP1P_, $_SDFFCE_NP1P_
	:verilog:`posedge` ``0``          ``0``          ``0``         $_DFFE_PN0N_, $_SDFFE_PN0N_, $_SDFFCE_PN0N_
	:verilog:`posedge` ``0``          ``0``          ``1``         $_DFFE_PN0P_, $_SDFFE_PN0P_, $_SDFFCE_PN0P_
	:verilog:`posedge` ``0``          ``1``          ``0``         $_DFFE_PN1N_, $_SDFFE_PN1N_, $_SDFFCE_PN1N_
	:verilog:`posedge` ``0``          ``1``          ``1``         $_DFFE_PN1P_, $_SDFFE_PN1P_, $_SDFFCE_PN1P_
	:verilog:`posedge` ``1``          ``0``          ``0``         $_DFFE_PP0N_, $_SDFFE_PP0N_, $_SDFFCE_PP0N_
	:verilog:`posedge` ``1``          ``0``          ``1``         $_DFFE_PP0P_, $_SDFFE_PP0P_, $_SDFFCE_PP0P_
	:verilog:`posedge` ``1``          ``1``          ``0``         $_DFFE_PP1N_, $_SDFFE_PP1N_, $_SDFFCE_PP1N_
	:verilog:`posedge` ``1``          ``1``          ``1``         $_DFFE_PP1P_, $_SDFFE_PP1P_, $_SDFFCE_PP1P_
	================== ============== ============== ============= ===========================================

.. table:: Cell types for gate level logic networks (FFs with set and reset)
	:name: tab:CellLib_gates_dffsr

	================== ============== ============== ============
	:math:`ClkEdge`    :math:`SetLvl` :math:`RstLvl` Cell Type
	================== ============== ============== ============
	:verilog:`negedge` ``0``          ``0``          $_DFFSR_NNN_
	:verilog:`negedge` ``0``          ``1``          $_DFFSR_NNP_
	:verilog:`negedge` ``1``          ``0``          $_DFFSR_NPN_
	:verilog:`negedge` ``1``          ``1``          $_DFFSR_NPP_
	:verilog:`posedge` ``0``          ``0``          $_DFFSR_PNN_
	:verilog:`posedge` ``0``          ``1``          $_DFFSR_PNP_
	:verilog:`posedge` ``1``          ``0``          $_DFFSR_PPN_
	:verilog:`posedge` ``1``          ``1``          $_DFFSR_PPP_
	================== ============== ============== ============


.. table:: Cell types for gate level logic networks (FFs with set and reset and enable)
	:name: tab:CellLib_gates_dffsre

	================== ============== ============== ============= ==============
	:math:`ClkEdge`    :math:`SetLvl` :math:`RstLvl` :math:`EnLvl` Cell Type
	================== ============== ============== ============= ==============
	:verilog:`negedge` ``0``          ``0``          ``0``         $_DFFSRE_NNNN_
	:verilog:`negedge` ``0``          ``0``          ``1``         $_DFFSRE_NNNP_
	:verilog:`negedge` ``0``          ``1``          ``0``         $_DFFSRE_NNPN_
	:verilog:`negedge` ``0``          ``1``          ``1``         $_DFFSRE_NNPP_
	:verilog:`negedge` ``1``          ``0``          ``0``         $_DFFSRE_NPNN_
	:verilog:`negedge` ``1``          ``0``          ``1``         $_DFFSRE_NPNP_
	:verilog:`negedge` ``1``          ``1``          ``0``         $_DFFSRE_NPPN_
	:verilog:`negedge` ``1``          ``1``          ``1``         $_DFFSRE_NPPP_
	:verilog:`posedge` ``0``          ``0``          ``0``         $_DFFSRE_PNNN_
	:verilog:`posedge` ``0``          ``0``          ``1``         $_DFFSRE_PNNP_
	:verilog:`posedge` ``0``          ``1``          ``0``         $_DFFSRE_PNPN_
	:verilog:`posedge` ``0``          ``1``          ``1``         $_DFFSRE_PNPP_
	:verilog:`posedge` ``1``          ``0``          ``0``         $_DFFSRE_PPNN_
	:verilog:`posedge` ``1``          ``0``          ``1``         $_DFFSRE_PPNP_
	:verilog:`posedge` ``1``          ``1``          ``0``         $_DFFSRE_PPPN_
	:verilog:`posedge` ``1``          ``1``          ``1``         $_DFFSRE_PPPP_
	================== ============== ============== ============= ==============


.. table:: Cell types for gate level logic networks (latches with reset)
	:name: tab:CellLib_gates_adlatch

	============= ============== ============== =============
	:math:`EnLvl` :math:`RstLvl` :math:`RstVal` Cell Type
	============= ============== ============== =============
	``0``         ``0``          ``0``          $_DLATCH_NN0_
	``0``         ``0``          ``1``          $_DLATCH_NN1_
	``0``         ``1``          ``0``          $_DLATCH_NP0_
	``0``         ``1``          ``1``          $_DLATCH_NP1_
	``1``         ``0``          ``0``          $_DLATCH_PN0_
	``1``         ``0``          ``1``          $_DLATCH_PN1_
	``1``         ``1``          ``0``          $_DLATCH_PP0_
	``1``         ``1``          ``1``          $_DLATCH_PP1_
	============= ============== ============== =============


.. table:: Cell types for gate level logic networks (latches with set and reset)
	:name: tab:CellLib_gates_dlatchsr

	============= ============== ============== ===============
	:math:`EnLvl` :math:`SetLvl` :math:`RstLvl` Cell Type
	============= ============== ============== ===============
	``0``         ``0``          ``0``          $_DLATCHSR_NNN_
	``0``         ``0``          ``1``          $_DLATCHSR_NNP_
	``0``         ``1``          ``0``          $_DLATCHSR_NPN_
	``0``         ``1``          ``1``          $_DLATCHSR_NPP_
	``1``         ``0``          ``0``          $_DLATCHSR_PNN_
	``1``         ``0``          ``1``          $_DLATCHSR_PNP_
	``1``         ``1``          ``0``          $_DLATCHSR_PPN_
	``1``         ``1``          ``1``          $_DLATCHSR_PPP_
	============= ============== ============== ===============



.. table:: Cell types for gate level logic networks (SR latches)
	:name: tab:CellLib_gates_sr

	============== ============== =========
	:math:`SetLvl` :math:`RstLvl` Cell Type
	============== ============== =========
	``0``          ``0``          $_SR_NN_
	``0``          ``1``          $_SR_NP_
	``1``          ``0``          $_SR_PN_
	``1``          ``1``          $_SR_PP_
	============== ============== =========


Tables \ :numref:`%s <tab:CellLib_gates>`, :numref:`%s
<tab:CellLib_gates_dffe>`, :numref:`%s <tab:CellLib_gates_adff>`, :numref:`%s
<tab:CellLib_gates_adffe>`, :numref:`%s <tab:CellLib_gates_dffsr>`, :numref:`%s
<tab:CellLib_gates_dffsre>`, :numref:`%s <tab:CellLib_gates_adlatch>`,
:numref:`%s <tab:CellLib_gates_dlatchsr>` and :numref:`%s
<tab:CellLib_gates_sr>` list all cell types used for gate level logic. The cell
types ``$_BUF_``, ``$_NOT_``, ``$_AND_``, ``$_NAND_``, ``$_ANDNOT_``, ``$_OR_``,
``$_NOR_``, ``$_ORNOT_``, ``$_XOR_``, ``$_XNOR_``, ``$_AOI3_``, ``$_OAI3_``,
``$_AOI4_``, ``$_OAI4_``, ``$_MUX_``, ``$_MUX4_``, ``$_MUX8_``, ``$_MUX16_`` and
``$_NMUX_`` are used to model combinatorial logic. The cell type ``$_TBUF_`` is
used to model tristate logic.

The ``$_MUX4_``, ``$_MUX8_`` and ``$_MUX16_`` cells are used to model wide
muxes, and correspond to the following Verilog code:

.. code-block:: verilog
	:force:

	// $_MUX4_
	assign Y = T ? (S ? D : C) :
	               (S ? B : A);
	// $_MUX8_
	assign Y = U ? T ? (S ? H : G) :
	                   (S ? F : E) :
	               T ? (S ? D : C) :
	                   (S ? B : A);
	// $_MUX16_
	assign Y = V ? U ? T ? (S ? P : O) :
	                       (S ? N : M) :
	                   T ? (S ? L : K) :
	                       (S ? J : I) :
	               U ? T ? (S ? H : G) :
	                       (S ? F : E) :
	                   T ? (S ? D : C) :
	                       (S ? B : A);

The cell types ``$_DFF_N_`` and ``$_DFF_P_`` represent d-type flip-flops.

The cell types ``$_DFFE_[NP][NP]_`` implement d-type flip-flops with enable. The
values in the table for these cell types relate to the following Verilog code
template.

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C)
		if (EN == EN_LVL)
			Q <= D;

The cell types ``$_DFF_[NP][NP][01]_`` implement d-type flip-flops with
asynchronous reset. The values in the table for these cell types relate to the
following Verilog code template, where ``RST_EDGE`` is ``posedge`` if
``RST_LVL`` if ``1``, and ``negedge`` otherwise.

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C, RST_EDGE R)
		if (R == RST_LVL)
			Q <= RST_VAL;
		else
			Q <= D;

The cell types ``$_SDFF_[NP][NP][01]_`` implement d-type flip-flops with
synchronous reset. The values in the table for these cell types relate to the
following Verilog code template:

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C)
		if (R == RST_LVL)
			Q <= RST_VAL;
		else
			Q <= D;

The cell types ``$_DFFE_[NP][NP][01][NP]_`` implement d-type flip-flops with
asynchronous reset and enable. The values in the table for these cell types
relate to the following Verilog code template, where ``RST_EDGE`` is
``posedge`` if ``RST_LVL`` if ``1``, and ``negedge`` otherwise.

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C, RST_EDGE R)
		if (R == RST_LVL)
			Q <= RST_VAL;
		else if (EN == EN_LVL)
			Q <= D;

The cell types ``$_SDFFE_[NP][NP][01][NP]_`` implement d-type flip-flops with
synchronous reset and enable, with reset having priority over enable. The values
in the table for these cell types relate to the following Verilog code template:

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C)
		if (R == RST_LVL)
			Q <= RST_VAL;
		else if (EN == EN_LVL)
			Q <= D;

The cell types ``$_SDFFCE_[NP][NP][01][NP]_`` implement d-type flip-flops with
synchronous reset and enable, with enable having priority over reset. The values
in the table for these cell types relate to the following Verilog code template:

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C)
		if (EN == EN_LVL)
			if (R == RST_LVL)
				Q <= RST_VAL;
			else
				Q <= D;

The cell types ``$_DFFSR_[NP][NP][NP]_`` implement d-type flip-flops with
asynchronous set and reset. The values in the table for these cell types relate
to the following Verilog code template, where ``RST_EDGE`` is ``posedge`` if
``RST_LVL`` if ``1``, ``negedge`` otherwise, and ``SET_EDGE`` is ``posedge``
if ``SET_LVL`` if ``1``, ``negedge`` otherwise.

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C, RST_EDGE R, SET_EDGE S)
		if (R == RST_LVL)
			Q <= 0;
		else if (S == SET_LVL)
			Q <= 1;
		else
			Q <= D;

The cell types ``$_DFFSRE_[NP][NP][NP][NP]_`` implement d-type flip-flops with
asynchronous set and reset and enable. The values in the table for these cell
types relate to the following Verilog code template, where ``RST_EDGE`` is
``posedge`` if ``RST_LVL`` if ``1``, ``negedge`` otherwise, and ``SET_EDGE``
is ``posedge`` if ``SET_LVL`` if ``1``, ``negedge`` otherwise.

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C, RST_EDGE R, SET_EDGE S)
		if (R == RST_LVL)
			Q <= 0;
		else if (S == SET_LVL)
			Q <= 1;
		else if (E == EN_LVL)
			Q <= D;

The cell types ``$_DLATCH_N_`` and ``$_DLATCH_P_`` represent d-type latches.

The cell types ``$_DLATCH_[NP][NP][01]_`` implement d-type latches with reset.
The values in the table for these cell types relate to the following Verilog
code template:

.. code-block:: verilog
	:force:

	always @*
		if (R == RST_LVL)
			Q <= RST_VAL;
		else if (E == EN_LVL)
			Q <= D;

The cell types ``$_DLATCHSR_[NP][NP][NP]_`` implement d-type latches with set
and reset. The values in the table for these cell types relate to the following
Verilog code template:

.. code-block:: verilog
	:force:

	always @*
		if (R == RST_LVL)
			Q <= 0;
		else if (S == SET_LVL)
			Q <= 1;
		else if (E == EN_LVL)
			Q <= D;

The cell types ``$_SR_[NP][NP]_`` implement sr-type latches. The values in the
table for these cell types relate to the following Verilog code template:

.. code-block:: verilog
	:force:

	always @*
		if (R == RST_LVL)
			Q <= 0;
		else if (S == SET_LVL)
			Q <= 1;

In most cases gate level logic networks are created from RTL networks using the
techmap pass. The flip-flop cells from the gate level logic network can be
mapped to physical flip-flop cells from a Liberty file using the dfflibmap pass.
The combinatorial logic cells can be mapped to physical cells from a Liberty
file via ABC using the abc pass.

Add information about ``$slice`` and ``$concat`` cells.

Add information about ``$lut`` and ``$sop`` cells.

Add information about ``$alu``, ``$macc``, ``$fa``, and ``$lcu`` cells.
