.. role:: verilog(code)
   :language: Verilog

.. _sec:memcells:

Memories
~~~~~~~~

Memories are either represented using ``RTLIL::Memory`` objects, `$memrd_v2`,
`$memwr_v2`, and `$meminit_v2` cells, or by `$mem_v2` cells alone.

In the first alternative the ``RTLIL::Memory`` objects hold the general metadata
for the memory (bit width, size in number of words, etc.) and for each port a
`$memrd_v2` (read port) or `$memwr_v2` (write port) cell is created. Having
individual cells for read and write ports has the advantage that they can be
consolidated using resource sharing passes. In some cases this drastically
reduces the number of required ports on the memory cell. In this alternative,
memory initialization data is represented by `$meminit_v2` cells, which allow
delaying constant folding for initialization addresses and data until after the
frontend finishes.

The `$memrd_v2` cells have a clock input ``CLK``, an enable input ``EN``, an
address input ``ADDR``, a data output ``DATA``, an asynchronous reset input
``ARST``, and a synchronous reset input ``SRST``. They also have the following
parameters:

``MEMID``
   The name of the ``RTLIL::Memory`` object that is associated with this read
   port.

``ABITS``
   The number of address bits (width of the ``ADDR`` input port).

``WIDTH``
   The number of data bits (width of the ``DATA`` output port).  Note that this
   may be a power-of-two multiple of the underlying memory's width -- such ports
   are called wide ports and access an aligned group of cells at once.  In this
   case, the corresponding low bits of ``ADDR`` must be tied to 0.

``CLK_ENABLE``
   When this parameter is non-zero, the clock is used. Otherwise this read port
   is asynchronous and the ``CLK`` input is not used.

``CLK_POLARITY``
   Clock is active on the positive edge if this parameter has the value ``1'b1``
   and on the negative edge if this parameter is ``1'b0``.

``TRANSPARENCY_MASK``
   This parameter is a bitmask of write ports that this read port is transparent
   with. The bits of this parameter are indexed by the write port's ``PORTID``
   parameter. Transparency can only be enabled between synchronous ports sharing
   a clock domain. When transparency is enabled for a given port pair, a read
   and write to the same address in the same cycle will return the new value.
   Otherwise the old value is returned.

``COLLISION_X_MASK``
   This parameter is a bitmask of write ports that have undefined collision
   behavior with this port. The bits of this parameter are indexed by the write
   port's ``PORTID`` parameter. This behavior can only be enabled between
   synchronous ports sharing a clock domain. When undefined collision is enabled
   for a given port pair, a read and write to the same address in the same cycle
   will return the undefined (all-X) value.This option is exclusive (for a given
   port pair) with the transparency option.

``ARST_VALUE``
   Whenever the ``ARST`` input is asserted, the data output will be reset to
   this value. Only used for synchronous ports.

``SRST_VALUE``
   Whenever the ``SRST`` input is synchronously asserted, the data output will
   be reset to this value. Only used for synchronous ports.

``INIT_VALUE``
   The initial value of the data output, for synchronous ports.

``CE_OVER_SRST``
   If this parameter is non-zero, the ``SRST`` input is only recognized when
   ``EN`` is true. Otherwise, ``SRST`` is recognized regardless of ``EN``.

The `$memwr_v2` cells have a clock input ``CLK``, an enable input ``EN`` (one
enable bit for each data bit), an address input ``ADDR`` and a data input
``DATA``. They also have the following parameters:

``MEMID``
   The name of the ``RTLIL::Memory`` object that is associated with this write
   port.

``ABITS``
   The number of address bits (width of the ``ADDR`` input port).

``WIDTH``
   The number of data bits (width of the ``DATA`` output port). Like with
   `$memrd_v2` cells, the width is allowed to be any power-of-two multiple of
   memory width, with the corresponding restriction on address.

``CLK_ENABLE``
   When this parameter is non-zero, the clock is used. Otherwise this write port
   is asynchronous and the ``CLK`` input is not used.

``CLK_POLARITY``
   Clock is active on positive edge if this parameter has the value ``1'b1`` and
   on the negative edge if this parameter is ``1'b0``.

``PORTID``
   An identifier for this write port, used to index write port bit mask
   parameters.

``PRIORITY_MASK``
   This parameter is a bitmask of write ports that this write port has priority
   over in case of writing to the same address.  The bits of this parameter are
   indexed by the other write port's ``PORTID`` parameter. Write ports can only
   have priority over write ports with lower port ID. When two ports write to
   the same address and neither has priority over the other, the result is
   undefined.  Priority can only be set between two synchronous ports sharing
   the same clock domain.

The `$meminit_v2` cells have an address input ``ADDR``, a data input ``DATA``,
with the width of the ``DATA`` port equal to ``WIDTH`` parameter times ``WORDS``
parameter, and a bit enable mask input ``EN`` with width equal to ``WIDTH``
parameter. All three of the inputs must resolve to a constant for synthesis to
succeed.

``MEMID``
   The name of the ``RTLIL::Memory`` object that is associated with this
   initialization cell.

``ABITS``
   The number of address bits (width of the ``ADDR`` input port).

``WIDTH``
   The number of data bits per memory location.

``WORDS``
   The number of consecutive memory locations initialized by this cell.

``PRIORITY``
   The cell with the higher integer value in this parameter wins an
   initialization conflict.

The HDL frontend models a memory using ``RTLIL::Memory`` objects and
asynchronous `$memrd_v2` and `$memwr_v2` cells. The `memory` pass (i.e. its
various sub-passes) migrates `$dff` cells into the `$memrd_v2` and `$memwr_v2`
cells making them synchronous, then converts them to a single `$mem_v2` cell and
(optionally) maps this cell type to `$dff` cells for the individual words and
multiplexer-based address decoders for the read and write interfaces. When the
last step is disabled or not possible, a `$mem_v2` cell is left in the design.

The `$mem_v2` cell provides the following parameters:

``MEMID``
   The name of the original ``RTLIL::Memory`` object that became this `$mem_v2`
   cell.

``SIZE``
   The number of words in the memory.

``ABITS``
   The number of address bits.

``WIDTH``
   The number of data bits per word.

``INIT``
   The initial memory contents.

``RD_PORTS``
   The number of read ports on this memory cell.

``RD_WIDE_CONTINUATION``
   This parameter is ``RD_PORTS`` bits wide, containing a bitmask of "wide
   continuation" read ports. Such ports are used to represent the extra data
   bits of wide ports in the combined cell, and must have all control signals
   identical with the preceding port, except for address, which must have the
   proper sub-cell address encoded in the low bits.

``RD_CLK_ENABLE``
   This parameter is ``RD_PORTS`` bits wide, containing a clock enable bit for
   each read port.

``RD_CLK_POLARITY``
   This parameter is ``RD_PORTS`` bits wide, containing a clock polarity bit for
   each read port.

``RD_TRANSPARENCY_MASK``
   This parameter is ``RD_PORTS*WR_PORTS`` bits wide, containing a concatenation
   of all ``TRANSPARENCY_MASK`` values of the original `$memrd_v2` cells.

``RD_COLLISION_X_MASK``
   This parameter is ``RD_PORTS*WR_PORTS`` bits wide, containing a concatenation
   of all ``COLLISION_X_MASK`` values of the original `$memrd_v2` cells.

``RD_CE_OVER_SRST``
   This parameter is ``RD_PORTS`` bits wide, determining relative synchronous
   reset and enable priority for each read port.

``RD_INIT_VALUE``
   This parameter is ``RD_PORTS*WIDTH`` bits wide, containing the initial value
   for each synchronous read port.

``RD_ARST_VALUE``
   This parameter is ``RD_PORTS*WIDTH`` bits wide, containing the asynchronous
   reset value for each synchronous read port.

``RD_SRST_VALUE``
   This parameter is ``RD_PORTS*WIDTH`` bits wide, containing the synchronous
   reset value for each synchronous read port.

``WR_PORTS``
   The number of write ports on this memory cell.

``WR_WIDE_CONTINUATION``
   This parameter is ``WR_PORTS`` bits wide, containing a bitmask of "wide
   continuation" write ports.

``WR_CLK_ENABLE``
   This parameter is ``WR_PORTS`` bits wide, containing a clock enable bit for
   each write port.

``WR_CLK_POLARITY``
   This parameter is ``WR_PORTS`` bits wide, containing a clock polarity bit for
   each write port.

``WR_PRIORITY_MASK``
   This parameter is ``WR_PORTS*WR_PORTS`` bits wide, containing a concatenation
   of all ``PRIORITY_MASK`` values of the original `$memwr_v2` cells.

The `$mem_v2` cell has the following ports:

``RD_CLK``
   This input is ``RD_PORTS`` bits wide, containing all clock signals for the
   read ports.

``RD_EN``
   This input is ``RD_PORTS`` bits wide, containing all enable signals for the
   read ports.

``RD_ADDR``
   This input is ``RD_PORTS*ABITS`` bits wide, containing all address signals
   for the read ports.

``RD_DATA``
   This output is ``RD_PORTS*WIDTH`` bits wide, containing all data signals for
   the read ports.

``RD_ARST``
   This input is ``RD_PORTS`` bits wide, containing all asynchronous reset
   signals for the read ports.

``RD_SRST``
   This input is ``RD_PORTS`` bits wide, containing all synchronous reset
   signals for the read ports.

``WR_CLK``
   This input is ``WR_PORTS`` bits wide, containing all clock signals for the
   write ports.

``WR_EN``
   This input is ``WR_PORTS*WIDTH`` bits wide, containing all enable signals for
   the write ports.

``WR_ADDR``
   This input is ``WR_PORTS*ABITS`` bits wide, containing all address signals
   for the write ports.

``WR_DATA``
   This input is ``WR_PORTS*WIDTH`` bits wide, containing all data signals for
   the write ports.

The `memory_collect` pass can be used to convert discrete `$memrd_v2`,
`$memwr_v2`, and `$meminit_v2` cells belonging to the same memory to a single
`$mem_v2` cell, whereas the `memory_unpack` pass performs the inverse operation.
The `memory_dff` pass can combine asynchronous memory ports that are fed by or
feeding registers into synchronous memory ports. The `memory_bram` pass can be
used to recognize `$mem_v2` cells that can be implemented with a block RAM
resource on an FPGA. The `memory_map` pass can be used to implement `$mem_v2`
cells as basic logic: word-wide DFFs and address decoders.

.. autocellgroup:: mem
   :members:
   :source:
   :linenos:
