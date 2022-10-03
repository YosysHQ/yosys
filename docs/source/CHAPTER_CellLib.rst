.. _chapter:celllib:

Internal Cell Library
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

RTL Cells
---------

Most of the RTL cells closely resemble the operators available in HDLs such as
Verilog or VHDL. Therefore Verilog operators are used in the following sections
to define the behaviour of the RTL cells.

Note that all RTL cells have parameters indicating the size of inputs and
outputs. When passes modify RTL cells they must always keep the values of these
parameters in sync with the size of the signals connected to the inputs and
outputs.

Simulation models for the RTL cells can be found in the file
techlibs/common/simlib.v in the Yosys source tree.

Unary Operators
~~~~~~~~~~~~~~~

All unary RTL cells have one input port and one output port. They also
have the following parameters:

-  | 
   | Set to a non-zero value if the input is signed and therefore should be
     sign-extended when needed.

-  | 
   | The width of the input port .

-  | 
   | The width of the output port .

:numref:`tab:CellLib_unary` lists all cells for unary RTL operators.

.. table:: Cell types for binary operators with their corresponding Verilog expressions.
	:name: tab:CellLib_unary

	=========== ============
	Verilog     Cell Type
	=========== ============
	``Y =  ~A`` $not
	``Y =  +A`` $pos
	``Y =  -A`` $neg
	``Y =  &A`` $reduce_and
	``Y =  |A`` $reduce_or
	``Y =  ^A`` $reduce_xor
	``Y = ~^A`` $reduce_xnor
	``Y =  |A`` $reduce_bool
	``Y =  !A`` $logic_not
	=========== ============

For the unary cells that output a logical value ($reduce_and, $reduce_or,
$reduce_xor, $reduce_xnor, $reduce_bool, $logic_not), when the parameter is
greater than 1, the output is zero-extended, and only the least significant bit
varies.

Note that $reduce_or and $reduce_bool actually represent the same logic
function. But the HDL frontends generate them in different situations. A
$reduce_or cell is generated when the prefix \| operator is being used. A
$reduce_bool cell is generated when a bit vector is used as a condition in an
if-statement or ?:-expression.

Binary Operators
~~~~~~~~~~~~~~~~

All binary RTL cells have two input ports and and one output port. They also
have the following parameters:

-  | 
   | Set to a non-zero value if the input is signed and therefore should be
     sign-extended when needed.

-  | 
   | The width of the input port .

-  | 
   | Set to a non-zero value if the input is signed and therefore should be
     sign-extended when needed.

-  | 
   | The width of the input port .

-  | 
   | The width of the output port .

:numref:`tab:CellLib_binary` lists all cells for binary RTL operators.

| ll Verilog & Cell Type
| ``Y = A  & B`` & $and
| ``Y = A  | B`` & $or
| ``Y = A  ^ B`` & $xor
| ``Y = A ~^ B`` & $xnor
| ``Y = A << B`` & $shl
| ``Y = A >> B`` & $shr
| ``Y = A <<< B`` & $sshl
| ``Y = A >>> B`` & $sshr
| ``Y = A && B`` & $logic_and
| ``Y = A || B`` & $logic_or
| ``Y = A === B`` & $eqx
| ``Y = A !== B`` & $nex

.. table:: Cell types for binary operators with their corresponding Verilog expressions.
	:name: tab:CellLib_binary

	===================== =========
	Verilog               Cell Type
	===================== =========
	``Y = A <  B``        $lt
	``Y = A <= B``        $le
	``Y = A == B``        $eq
	``Y = A != B``        $ne
	``Y = A >= B``        $ge
	``Y = A >  B``        $gt
	``Y = A  + B``        $add
	``Y = A  - B``        $sub
	``Y = A  * B``        $mul
	``Y = A  / B``        $div
	``Y = A  % B`` & $mod $divfloor
	\                     $modfoor
	``Y = A ** B``        $pow
	===================== =========

The $shl and $shr cells implement logical shifts, whereas the $sshl and $sshr
cells implement arithmetic shifts. The $shl and $sshl cells implement the same
operation. All four of these cells interpret the second operand as unsigned, and
require to be zero.

Two additional shift operator cells are available that do not directly
correspond to any operator in Verilog, $shift and $shiftx. The $shift cell
performs a right logical shift if the second operand is positive (or unsigned),
and a left logical shift if it is negative. The $shiftx cell performs the same
operation as the $shift cell, but the vacated bit positions are filled with
undef (x) bits, and corresponds to the Verilog indexed part-select expression.

For the binary cells that output a logical value ($logic_and, $logic_or, $eqx,
$nex, $lt, $le, $eq, $ne, $ge, $gt), when the parameter is greater than 1, the
output is zero-extended, and only the least significant bit varies.

Division and modulo cells are available in two rounding modes. The original $div
and $mod cells are based on truncating division, and correspond to the semantics
of the verilog / and % operators. The $divfloor and $modfloor cells represent
flooring division and flooring modulo, the latter of which is also known as
"remainder" in several languages. See :numref:`tab:CellLib_divmod` for a
side-by-side comparison between the different semantics.

.. table:: Comparison between different rounding modes for division and modulo cells.
	:name: tab:CellLib_divmod

	======== ==== ==== ==== ========= =========
	\                                
	\             $div $mod $divfloor $modfloor
	-10 / 3  -3.3 -3   -1   -4        2
	10 / -3  -3.3 -3   1    -4        -2
	-10 / -3 3.3  3    -1   3         -1
	10 / 3   3.3  3    1    3         1
	======== ==== ==== ==== ========= =========

Multiplexers
~~~~~~~~~~~~

Multiplexers are generated by the Verilog HDL frontend for ?:-expressions.
Multiplexers are also generated by the proc pass to map the decision trees from
RTLIL::Process objects to logic.

The simplest multiplexer cell type is $mux. Cells of this type have a parameter
and data inputs and and a data output , all of the specified width. This cell
also has a single bit control input . If is 0 the value from the input is sent
to the output, if it is 1 the value from the input is sent to the output. So the
$mux cell implements the function ``Y = S ? B : A``.

The $pmux cell is used to multiplex between many inputs using a one-hot select
signal. Cells of this type have a and a parameter and inputs , , and and an
output . The input is bits wide. The input and the output are both bits wide and
the input is \* bits wide. When all bits of are zero, the value from input is
sent to the output. If the :math:`n`\ 'th bit from is set, the value :math:`n`\
'th bits wide slice of the input is sent to the output. When more than one bit
from is set the output is undefined. Cells of this type are used to model
"parallel cases" (defined by using the parallel_case attribute or detected by an
optimization).

The $tribuf cell is used to implement tristate logic. Cells of this type have a
parameter and inputs and and an output . The input and output are bits wide, and
the input is one bit wide. When is 0, the output is not driven. When is 1, the
value from input is sent to the output. Therefore, the $tribuf cell implements
the function ``Y = EN ? A : 'bz``.

Behavioural code with cascaded if-then-else- and case-statements usually results
in trees of multiplexer cells. Many passes (from various optimizations to FSM
extraction) heavily depend on these multiplexer trees to understand dependencies
between signals. Therefore optimizations should not break these multiplexer
trees (e.g. by replacing a multiplexer between a calculated signal and a
constant zero with an $and gate).

Registers
~~~~~~~~~

SR-type latches are represented by $sr cells. These cells have input ports and
and an output port. They have the following parameters:

-  | 
   | The width of inputs and and output .

-  | 
   | The set input bits are active-high if this parameter has the value 1'b1 and
     active-low if this parameter is 1'b0.

-  | 
   | The reset input bits are active-high if this parameter has the value 1'b1
     and active-low if this parameter is 1'b0.

Both set and reset inputs have separate bits for every output bit. When both the
set and reset inputs of an $sr cell are active for a given bit index, the reset
input takes precedence.

D-type flip-flops are represented by $dff cells. These cells have a clock port ,
an input port and an output port . The following parameters are available for
$dff cells:

-  | 
   | The width of input and output .

-  | 
   | Clock is active on the positive edge if this parameter has the value 1'b1
     and on the negative edge if this parameter is 1'b0.

D-type flip-flops with asynchronous reset are represented by $adff cells. As the
$dff cells they have , and ports. In addition they also have a single-bit input
port for the reset pin and the following additional two parameters:

-  | 
   | The asynchronous reset is active-high if this parameter has the value 1'b1
     and active-low if this parameter is 1'b0.

-  | 
   | The state of will be set to this value when the reset is active.

Usually these cells are generated by the proc pass using the information in the
designs RTLIL::Process objects.

D-type flip-flops with synchronous reset are represented by $sdff cells. As the
$dff cells they have , and ports. In addition they also have a single-bit input
port for the reset pin and the following additional two parameters:

-  | 
   | The synchronous reset is active-high if this parameter has the value 1'b1
     and active-low if this parameter is 1'b0.

-  | 
   | The state of will be set to this value when the reset is active.

Note that the $adff and $sdff cells can only be used when the reset value is
constant.

D-type flip-flops with asynchronous load are represented by $aldff cells. As the
$dff cells they have , and ports. In addition they also have a single-bit input
port for the async load enable pin, a input port with the same width as data for
the async load data, and the following additional parameter:

-  | 
   | The asynchronous load is active-high if this parameter has the value 1'b1
     and active-low if this parameter is 1'b0.

D-type flip-flops with asynchronous set and reset are represented by $dffsr
cells. As the $dff cells they have , and ports. In addition they also have
multi-bit and input ports and the corresponding polarity parameters, like $sr
cells.

D-type flip-flops with enable are represented by $dffe, $adffe, $aldffe,
$dffsre, $sdffe, and $sdffce cells, which are enhanced variants of $dff, $adff,
$aldff, $dffsr, $sdff (with reset over enable) and $sdff (with enable over
reset) cells, respectively. They have the same ports and parameters as their
base cell. In addition they also have a single-bit input port for the enable pin
and the following parameter:

-  | 
   | The enable input is active-high if this parameter has the value 1'b1 and
     active-low if this parameter is 1'b0.

D-type latches are represented by $dlatch cells. These cells have an enable port
, an input port , and an output port . The following parameters are available
for $dlatch cells:

-  | 
   | The width of input and output .

-  | 
   | The enable input is active-high if this parameter has the value 1'b1 and
     active-low if this parameter is 1'b0.

The latch is transparent when the input is active.

D-type latches with reset are represented by $adlatch cells. In addition to
$dlatch ports and parameters, they also have a single-bit input port for the
reset pin and the following additional parameters:

-  | 
   | The asynchronous reset is active-high if this parameter has the value 1'b1
     and active-low if this parameter is 1'b0.

-  | 
   | The state of will be set to this value when the reset is active.

D-type latches with set and reset are represented by $dlatchsr cells. In
addition to $dlatch ports and parameters, they also have multi-bit and input
ports and the corresponding polarity parameters, like $sr cells.

.. _sec:memcells:

Memories
~~~~~~~~

Memories are either represented using RTLIL::Memory objects, $memrd_v2,
$memwr_v2, and $meminit_v2 cells, or by $mem_v2 cells alone.

In the first alternative the RTLIL::Memory objects hold the general metadata for
the memory (bit width, size in number of words, etc.) and for each port a
$memrd_v2 (read port) or $memwr_v2 (write port) cell is created. Having
individual cells for read and write ports has the advantage that they can be
consolidated using resource sharing passes. In some cases this drastically
reduces the number of required ports on the memory cell. In this alternative,
memory initialization data is represented by $meminit_v2 cells, which allow
delaying constant folding for initialization addresses and data until after the
frontend finishes.

The $memrd_v2 cells have a clock input , an enable input , an address input , a
data output , an asynchronous reset input , and a synchronous reset input . They
also have the following parameters:

-  | 
   | The name of the RTLIL::Memory object that is associated with this read
     port.

-  | 
   | The number of address bits (width of the input port).

-  | 
   | The number of data bits (width of the output port). Note that this may be a
     power-of-two multiple of the underlying memory's width – such ports are
     called wide ports and access an aligned group of cells at once. In this
     case, the corresponding low bits of must be tied to 0.

-  | 
   | When this parameter is non-zero, the clock is used. Otherwise this read
     port is asynchronous and the input is not used.

-  | 
   | Clock is active on the positive edge if this parameter has the value 1'b1
     and on the negative edge if this parameter is 1'b0.

-  | 
   | This parameter is a bitmask of write ports that this read port is
     transparent with. The bits of this parameter are indexed by the write
     port's parameter. Transparency can only be enabled between synchronous
     ports sharing a clock domain. When transparency is enabled for a given port
     pair, a read and write to the same address in the same cycle will return
     the new value. Otherwise the old value is returned.

-  | 
   | This parameter is a bitmask of write ports that have undefined collision
     behavior with this port. The bits of this parameter are indexed by the
     write port's parameter. This behavior can only be enabled between
     synchronous ports sharing a clock domain. When undefined collision is
     enabled for a given port pair, a read and write to the same address in the
     same cycle will return the undefined (all-X) value. This option is
     exclusive (for a given port pair) with the transparency option.

-  | 
   | Whenever the input is asserted, the data output will be reset to this
     value. Only used for synchronous ports.

-  | 
   | Whenever the input is synchronously asserted, the data output will be reset
     to this value. Only used for synchronous ports.

-  | 
   | The initial value of the data output, for synchronous ports.

-  | 
   | If this parameter is non-zero, the input is only recognized when is true.
     Otherwise, is recognized regardless of .

The $memwr_v2 cells have a clock input , an enable input (one enable bit for
each data bit), an address input and a data input . They also have the following
parameters:

-  | 
   | The name of the RTLIL::Memory object that is associated with this write
     port.

-  | 
   | The number of address bits (width of the input port).

-  | 
   | The number of data bits (width of the output port). Like with $memrd_v2
     cells, the width is allowed to be any power-of-two multiple of memory
     width, with the corresponding restriction on address.

-  | 
   | When this parameter is non-zero, the clock is used. Otherwise this write
     port is asynchronous and the input is not used.

-  | 
   | Clock is active on positive edge if this parameter has the value 1'b1 and
     on the negative edge if this parameter is 1'b0.

-  | 
   | An identifier for this write port, used to index write port bit mask
     parameters.

-  | 
   | This parameter is a bitmask of write ports that this write port has
     priority over in case of writing to the same address. The bits of this
     parameter are indexed by the other write port's parameter. Write ports can
     only have priority over write ports with lower port ID. When two ports
     write to the same address and neither has priority over the other, the
     result is undefined. Priority can only be set between two synchronous ports
     sharing the same clock domain.

The $meminit_v2 cells have an address input , a data input , with the width of
the port equal to parameter times parameter, and a bit enable mask input with
width equal to parameter. All three of the inputs must resolve to a constant for
synthesis to succeed.

-  | 
   | The name of the RTLIL::Memory object that is associated with this
     initialization cell.

-  | 
   | The number of address bits (width of the input port).

-  | 
   | The number of data bits per memory location.

-  | 
   | The number of consecutive memory locations initialized by this cell.

-  | 
   | The cell with the higher integer value in this parameter wins an
     initialization conflict.

The HDL frontend models a memory using RTLIL::Memory objects and asynchronous
$memrd_v2 and $memwr_v2 cells. The memory pass (i.e. its various sub-passes)
migrates $dff cells into the $memrd_v2 and $memwr_v2 cells making them
synchronous, then converts them to a single $mem_v2 cell and (optionally) maps
this cell type to $dff cells for the individual words and multiplexer-based
address decoders for the read and write interfaces. When the last step is
disabled or not possible, a $mem_v2 cell is left in the design.

The $mem_v2 cell provides the following parameters:

-  | 
   | The name of the original RTLIL::Memory object that became this $mem_v2
     cell.

-  | 
   | The number of words in the memory.

-  | 
   | The number of address bits.

-  | 
   | The number of data bits per word.

-  | 
   | The initial memory contents.

-  | 
   | The number of read ports on this memory cell.

-  | 
   | This parameter is bits wide, containing a bitmask of "wide continuation"
     read ports. Such ports are used to represent the extra data bits of wide
     ports in the combined cell, and must have all control signals identical
     with the preceding port, except for address, which must have the proper
     sub-cell address encoded in the low bits.

-  | 
   | This parameter is bits wide, containing a clock enable bit for each read
     port.

-  | 
   | This parameter is bits wide, containing a clock polarity bit for each read
     port.

-  | 
   | This parameter is bits wide, containing a concatenation of all values of
     the original $memrd_v2 cells.

-  | 
   | This parameter is bits wide, containing a concatenation of all values of
     the original $memrd_v2 cells.

-  | 
   | This parameter is bits wide, determining relative synchronous reset and
     enable priority for each read port.

-  | 
   | This parameter is bits wide, containing the initial value for each
     synchronous read port.

-  | 
   | This parameter is bits wide, containing the asynchronous reset value for
     each synchronous read port.

-  | 
   | This parameter is bits wide, containing the synchronous reset value for
     each synchronous read port.

-  | 
   | The number of write ports on this memory cell.

-  | 
   | This parameter is bits wide, containing a bitmask of "wide continuation"
     write ports.

-  | 
   | This parameter is bits wide, containing a clock enable bit for each write
     port.

-  | 
   | This parameter is bits wide, containing a clock polarity bit for each write
     port.

-  | 
   | This parameter is bits wide, containing a concatenation of all values of
     the original $memwr_v2 cells.

The $mem_v2 cell has the following ports:

-  | 
   | This input is bits wide, containing all clock signals for the read ports.

-  | 
   | This input is bits wide, containing all enable signals for the read ports.

-  | 
   | This input is \* bits wide, containing all address signals for the read
     ports.

-  | 
   | This input is \* bits wide, containing all data signals for the read ports.

-  | 
   | This input is bits wide, containing all asynchronous reset signals for the
     read ports.

-  | 
   | This input is bits wide, containing all synchronous reset signals for the
     read ports.

-  | 
   | This input is bits wide, containing all clock signals for the write ports.

-  | 
   | This input is \* bits wide, containing all enable signals for the write
     ports.

-  | 
   | This input is \* bits wide, containing all address signals for the write
     ports.

-  | 
   | This input is \* bits wide, containing all data signals for the write
     ports.

The memory_collect pass can be used to convert discrete $memrd_v2, $memwr_v2,
and $meminit_v2 cells belonging to the same memory to a single $mem_v2 cell,
whereas the memory_unpack pass performs the inverse operation. The memory_dff
pass can combine asynchronous memory ports that are fed by or feeding registers
into synchronous memory ports. The memory_bram pass can be used to recognize
$mem_v2 cells that can be implemented with a block RAM resource on an FPGA. The
memory_map pass can be used to implement $mem_v2 cells as basic logic: word-wide
DFFs and address decoders.

Finite State Machines
~~~~~~~~~~~~~~~~~~~~~

Add a brief description of the $fsm cell type.

Specify rules
~~~~~~~~~~~~~

Add information about $specify2, $specify3, and $specrule cells.

Formal verification cells
~~~~~~~~~~~~~~~~~~~~~~~~~

Add information about $assert, $assume, $live, $fair, $cover, $equiv,
$initstate, $anyconst, $anyseq, $anyinit, $allconst, $allseq cells.

Add information about $ff and $_FF\_ cells.

.. _sec:celllib_gates:

Gates
-----

For gate level logic networks, fixed function single bit cells are used that do
not provide any parameters.

Simulation models for these cells can be found in the file
techlibs/common/simcells.v in the Yosys source tree.

.. table:: Cell types for gate level logic networks (main list)
	:name: tab:CellLib_gates

	================================ ============
	Verilog                          Cell Type
	================================ ============
	``Y = A``                        _BUF\_
	``Y = ~A``                       _NOT\_
	``Y = A & B``                    _AND\_
	``Y = ~(A & B)``                 _NAND\_
	``Y = A & ~B``                   _ANDNOT\_
	``Y = A | B``                    _OR\_
	``Y = ~(A | B)``                 _NOR\_
	``Y = A | ~B``                   _ORNOT\_
	``Y = A ^ B``                    _XOR\_
	``Y = ~(A ^ B)``                 _XNOR\_
	``Y = ~((A & B) | C)``           _AOI3\_
	``Y = ~((A | B) & C)``           _OAI3\_
	``Y = ~((A & B) | (C & D))``     _AOI4\_
	``Y = ~((A | B) & (C | D))``     _OAI4\_
	``Y = S ? B : A``                _MUX\_
	``Y = ~(S ? B : A)``             _NMUX\_
	(see below)                      _MUX4\_
	(see below)                      _MUX8\_
	(see below)                      _MUX16\_
	``Y = EN ? A : 1'bz``            _TBUF\_
	``always @(negedge C) Q <= D``   _DFF_N\_
	``always @(posedge C) Q <= D``   _DFF_P\_
	``always @* if (!E) Q <= D``     _DLATCH_N\_
	``always @* if (E)  Q <= D``     _DLATCH_P\_
	================================ ============

.. table:: Cell types for gate level logic networks (FFs with reset)
	:name: tab:CellLib_gates_adff

	=============== ============== ============== =========================
	:math:`ClkEdge` :math:`RstLvl` :math:`RstVal` Cell Type
	=============== ============== ============== =========================
	``negedge``     ``0``          ``0``          $_DFF_NN0\_, $_SDFF_NN0\_
	``negedge``     ``0``          ``1``          $_DFF_NN1\_, $_SDFF_NN1\_
	``negedge``     ``1``          ``0``          $_DFF_NP0\_, $_SDFF_NP0\_
	``negedge``     ``1``          ``1``          $_DFF_NP1\_, $_SDFF_NP1\_
	``posedge``     ``0``          ``0``          $_DFF_PN0\_, $_SDFF_PN0\_
	``posedge``     ``0``          ``1``          $_DFF_PN1\_, $_SDFF_PN1\_
	``posedge``     ``1``          ``0``          $_DFF_PP0\_, $_SDFF_PP0\_
	``posedge``     ``1``          ``1``          $_DFF_PP1\_, $_SDFF_PP1\_
	=============== ============== ============== =========================


.. table:: Cell types for gate level logic networks (FFs with enable)
	:name: tab:CellLib_gates_dffe

	=============== ============= ===========
	:math:`ClkEdge` :math:`EnLvl` Cell Type
	=============== ============= ===========
	``negedge``     ``0``         $_DFFE_NN\_
	``negedge``     ``1``         $_DFFE_NP\_
	``posedge``     ``0``         $_DFFE_PN\_
	``posedge``     ``1``         $_DFFE_PP\_
	=============== ============= ===========


.. table:: Cell types for gate level logic networks (FFs with reset and enable)
	:name: tab:CellLib_gates_adffe

	=============== ============== ============== ============= ==============================================
	:math:`ClkEdge` :math:`RstLvl` :math:`RstVal` :math:`EnLvl` Cell Type
	=============== ============== ============== ============= ==============================================
	``negedge``     ``0``          ``0``          ``0``         $_DFFE_NN0N\_, $_SDFFE_NN0N\_, $_SDFFCE_NN0N\_
	``negedge``     ``0``          ``0``          ``1``         $_DFFE_NN0P\_, $_SDFFE_NN0P\_, $_SDFFCE_NN0P\_
	``negedge``     ``0``          ``1``          ``0``         $_DFFE_NN1N\_, $_SDFFE_NN1N\_, $_SDFFCE_NN1N\_
	``negedge``     ``0``          ``1``          ``1``         $_DFFE_NN1P\_, $_SDFFE_NN1P\_, $_SDFFCE_NN1P\_
	``negedge``     ``1``          ``0``          ``0``         $_DFFE_NP0N\_, $_SDFFE_NP0N\_, $_SDFFCE_NP0N\_
	``negedge``     ``1``          ``0``          ``1``         $_DFFE_NP0P\_, $_SDFFE_NP0P\_, $_SDFFCE_NP0P\_
	``negedge``     ``1``          ``1``          ``0``         $_DFFE_NP1N\_, $_SDFFE_NP1N\_, $_SDFFCE_NP1N\_
	``negedge``     ``1``          ``1``          ``1``         $_DFFE_NP1P\_, $_SDFFE_NP1P\_, $_SDFFCE_NP1P\_
	``posedge``     ``0``          ``0``          ``0``         $_DFFE_PN0N\_, $_SDFFE_PN0N\_, $_SDFFCE_PN0N\_
	``posedge``     ``0``          ``0``          ``1``         $_DFFE_PN0P\_, $_SDFFE_PN0P\_, $_SDFFCE_PN0P\_
	``posedge``     ``0``          ``1``          ``0``         $_DFFE_PN1N\_, $_SDFFE_PN1N\_, $_SDFFCE_PN1N\_
	``posedge``     ``0``          ``1``          ``1``         $_DFFE_PN1P\_, $_SDFFE_PN1P\_, $_SDFFCE_PN1P\_
	``posedge``     ``1``          ``0``          ``0``         $_DFFE_PP0N\_, $_SDFFE_PP0N\_, $_SDFFCE_PP0N\_
	``posedge``     ``1``          ``0``          ``1``         $_DFFE_PP0P\_, $_SDFFE_PP0P\_, $_SDFFCE_PP0P\_
	``posedge``     ``1``          ``1``          ``0``         $_DFFE_PP1N\_, $_SDFFE_PP1N\_, $_SDFFCE_PP1N\_
	``posedge``     ``1``          ``1``          ``1``         $_DFFE_PP1P\_, $_SDFFE_PP1P\_, $_SDFFCE_PP1P\_
	=============== ============== ============== ============= ==============================================

.. table:: Cell types for gate level logic networks (FFs with set and reset)
	:name: tab:CellLib_gates_dffsr

	=============== ============== ============== =============
	:math:`ClkEdge` :math:`SetLvl` :math:`RstLvl` Cell Type
	=============== ============== ============== =============
	``negedge``     ``0``          ``0``          $_DFFSR_NNN\_
	``negedge``     ``0``          ``1``          $_DFFSR_NNP\_
	``negedge``     ``1``          ``0``          $_DFFSR_NPN\_
	``negedge``     ``1``          ``1``          $_DFFSR_NPP\_
	``posedge``     ``0``          ``0``          $_DFFSR_PNN\_
	``posedge``     ``0``          ``1``          $_DFFSR_PNP\_
	``posedge``     ``1``          ``0``          $_DFFSR_PPN\_
	``posedge``     ``1``          ``1``          $_DFFSR_PPP\_
	=============== ============== ============== =============


.. table:: Cell types for gate level logic networks (FFs with set and reset and enable)
	:name: tab:CellLib_gates_dffsre

	=============== ============== ============== ============= ===============
	:math:`ClkEdge` :math:`SetLvl` :math:`RstLvl` :math:`EnLvl` Cell Type
	=============== ============== ============== ============= ===============
	``negedge``     ``0``          ``0``          ``0``         $_DFFSRE_NNNN\_
	``negedge``     ``0``          ``0``          ``1``         $_DFFSRE_NNNP\_
	``negedge``     ``0``          ``1``          ``0``         $_DFFSRE_NNPN\_
	``negedge``     ``0``          ``1``          ``1``         $_DFFSRE_NNPP\_
	``negedge``     ``1``          ``0``          ``0``         $_DFFSRE_NPNN\_
	``negedge``     ``1``          ``0``          ``1``         $_DFFSRE_NPNP\_
	``negedge``     ``1``          ``1``          ``0``         $_DFFSRE_NPPN\_
	``negedge``     ``1``          ``1``          ``1``         $_DFFSRE_NPPP\_
	``posedge``     ``0``          ``0``          ``0``         $_DFFSRE_PNNN\_
	``posedge``     ``0``          ``0``          ``1``         $_DFFSRE_PNNP\_
	``posedge``     ``0``          ``1``          ``0``         $_DFFSRE_PNPN\_
	``posedge``     ``0``          ``1``          ``1``         $_DFFSRE_PNPP\_
	``posedge``     ``1``          ``0``          ``0``         $_DFFSRE_PPNN\_
	``posedge``     ``1``          ``0``          ``1``         $_DFFSRE_PPNP\_
	``posedge``     ``1``          ``1``          ``0``         $_DFFSRE_PPPN\_
	``posedge``     ``1``          ``1``          ``1``         $_DFFSRE_PPPP\_
	=============== ============== ============== ============= ===============


.. table:: Cell types for gate level logic networks (latches with reset)
	:name: tab:CellLib_gates_adlatch

	============= ============== ============== ==============
	:math:`EnLvl` :math:`RstLvl` :math:`RstVal` Cell Type
	============= ============== ============== ==============
	``0``         ``0``          ``0``          $_DLATCH_NN0\_
	``0``         ``0``          ``1``          $_DLATCH_NN1\_
	``0``         ``1``          ``0``          $_DLATCH_NP0\_
	``0``         ``1``          ``1``          $_DLATCH_NP1\_
	``1``         ``0``          ``0``          $_DLATCH_PN0\_
	``1``         ``0``          ``1``          $_DLATCH_PN1\_
	``1``         ``1``          ``0``          $_DLATCH_PP0\_
	``1``         ``1``          ``1``          $_DLATCH_PP1\_
	============= ============== ============== ==============


.. table:: Cell types for gate level logic networks (latches with set and reset)
	:name: tab:CellLib_gates_dlatchsr

	============= ============== ============== ================
	:math:`EnLvl` :math:`SetLvl` :math:`RstLvl` Cell Type
	============= ============== ============== ================
	``0``         ``0``          ``0``          $_DLATCHSR_NNN\_
	``0``         ``0``          ``1``          $_DLATCHSR_NNP\_
	``0``         ``1``          ``0``          $_DLATCHSR_NPN\_
	``0``         ``1``          ``1``          $_DLATCHSR_NPP\_
	``1``         ``0``          ``0``          $_DLATCHSR_PNN\_
	``1``         ``0``          ``1``          $_DLATCHSR_PNP\_
	``1``         ``1``          ``0``          $_DLATCHSR_PPN\_
	``1``         ``1``          ``1``          $_DLATCHSR_PPP\_
	============= ============== ============== ================



.. table:: Cell types for gate level logic networks (SR latches)
	:name: tab:CellLib_gates_sr

	============== ============== =========
	:math:`SetLvl` :math:`RstLvl` Cell Type
	============== ============== =========
	``0``          ``0``          $_SR_NN\_
	``0``          ``1``          $_SR_NP\_
	``1``          ``0``          $_SR_PN\_
	``1``          ``1``          $_SR_PP\_
	============== ============== =========


Tables \ :numref:`%s <tab:CellLib_gates>`, :numref:`%s <tab:CellLib_gates_dffe>`,
:numref:`%s <tab:CellLib_gates_adff>`, :numref:`%s <tab:CellLib_gates_adffe>`,
:numref:`%s <tab:CellLib_gates_dffsr>`, :numref:`%s <tab:CellLib_gates_dffsre>`,
:numref:`%s <tab:CellLib_gates_adlatch>`, 
:numref:`%s <tab:CellLib_gates_dlatchsr>` and :numref:`%s <tab:CellLib_gates_sr>` 
list all cell types used for gate level logic. The cell types $_BUF\_, $_NOT\_,
$_AND\_, $_NAND\_, $_ANDNOT\_, $_OR\_, $_NOR\_, $_ORNOT\_, $_XOR\_, $_XNOR\_,
$_AOI3\_, $_OAI3\_, $_AOI4\_, $_OAI4\_, $_MUX\_, $_MUX4\_, $_MUX8\_, $_MUX16\_
and $_NMUX\_ are used to model combinatorial logic. The cell type $_TBUF\_ is
used to model tristate logic.

The $_MUX4\_, $_MUX8\_ and $_MUX16\_ cells are used to model wide muxes, and
correspond to the following Verilog code:

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

The cell types $_DFF_N\_ and $_DFF_P\_ represent d-type flip-flops.

The cell types $_DFFE_[NP][NP]\_ implement d-type flip-flops with enable. The
values in the table for these cell types relate to the following Verilog code
template.

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C)
		if (EN == EN_LVL)
			Q <= D;

The cell types $_DFF_[NP][NP][01]\_ implement d-type flip-flops with
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

The cell types $_SDFF_[NP][NP][01]\_ implement d-type flip-flops with
synchronous reset. The values in the table for these cell types relate to the
following Verilog code template:

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C)
		if (R == RST_LVL)
			Q <= RST_VAL;
		else
			Q <= D;

The cell types $_DFFE_[NP][NP][01][NP]\_ implement d-type flip-flops with
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

The cell types $_SDFFE_[NP][NP][01][NP]\_ implement d-type flip-flops with
synchronous reset and enable, with reset having priority over enable. The values
in the table for these cell types relate to the following Verilog code template:

.. code-block:: verilog
	:force:

	always @(CLK_EDGE C)
		if (R == RST_LVL)
			Q <= RST_VAL;
		else if (EN == EN_LVL)
			Q <= D;

The cell types $_SDFFCE_[NP][NP][01][NP]\_ implement d-type flip-flops with
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

The cell types $_DFFSR_[NP][NP][NP]\_ implement d-type flip-flops with
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

The cell types $_DFFSRE_[NP][NP][NP][NP]\_ implement d-type flip-flops with
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

The cell types $_DLATCH_N\_ and $_DLATCH_P\_ represent d-type latches.

The cell types $_DLATCH_[NP][NP][01]\_ implement d-type latches with reset. The
values in the table for these cell types relate to the following Verilog code
template:

.. code-block:: verilog
	:force:

	always @*
		if (R == RST_LVL)
			Q <= RST_VAL;
		else if (E == EN_LVL)
			Q <= D;

The cell types $_DLATCHSR_[NP][NP][NP]\_ implement d-type latches with set and
reset. The values in the table for these cell types relate to the following
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

The cell types $_SR_[NP][NP]\_ implement sr-type latches. The values in the
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

Add information about $slice and $concat cells.

Add information about $lut and $sop cells.

Add information about $alu, $macc, $fa, and $lcu cells.
