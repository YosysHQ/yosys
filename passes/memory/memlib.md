# The `memory_libmap` pass

The `memory_libmap` pass is used to map memories to hardware primitives.  To work,
it needs a description of available target memories in a custom format.


## Basic structure

A basic library could look like this:

    # A distributed-class RAM called $__RAM16X4SDP_
    ram distributed $__RAM16X4SDP_ {
        # Has 4 address bits (ie. 16 rows).
        abits 4;
        # Has 4 data bits.
        width 4;
        # Cost for the selection heuristic.
        cost 4;
        # Can be initialized to any value on startup.
        init any;
        # Has a synchronous write port called "W"...
        port sw "W" {
            # ... with a positive edge clock.
            clock posedge;
        }
        # Has an asynchronous read port called "R".
        port ar "R" {
        }
    }

    # A block-class RAM called $__RAMB9K_
    ram block $__RAMB9K_ {
        # Has 13 address bits in the base (most narrow) data width.
        abits 13;
        # The available widths are:
        # - 1 (13 address bits)
        # - 2 (12 address bits)
        # - 4 (11 address bits)
        # - 9 (10 address bits)
        # - 18 (9 address bits)
        # The width selection is per-port.
        widths 1 2 4 9 18 per_port;
        # Has a write enable signal with 1 bit for every 9 data bits.
        byte 9;
        cost 64;
        init any;
        # Has two synchronous read+write ports, called "A" and "B".
        port srsw "A" "B" {
            clock posedge;
            # Has a clock enable signal (gates both read and write).
            clken;
            # Has three per-port selectable options for handling read+write behavior:
            portoption "RDWR" "NO_CHANGE" {
                # When port is writing, reading is not done (output register keeps
                # its value).
                rdwr no_change;
            }
            portoption "RDWR" "OLD" {
                # When port is writing, the data read is the old value (before the
                # write).
                rdwr old;
            }
            portoption "RDWR" "NEW" {
                # When port is writing, the data read is the new value.
                rdwr new;
            }
        }
    }

The pass will automatically select between the two available cells and
the logic fallback (mapping the whole memory to LUTs+FFs) based on required
capabilities and cost function.  The selected memories will be transformed
to intermediate `$__RAM16X4SDP_` and `$__RAMB9K_` cells that need to be mapped
to actual hardware cells by a `techmap` pass, while memories selected for logic
fallback will be left unmapped and will be later mopped up by `memory_map` pass.

## RAM definition blocks

The syntax for a RAM definition is:

    ram <kind: distributed|block|huge> <name> {
        <ram properties>
        <ports>
    }

The `<name>` is used as the type of the mapped cell that will be passed to `techmap`.
The memory kind is one of `distributed`, `block`, or `huge`.  It describes the general
class of the memory and can be matched on by manual selection attributes.

The available ram properties are:

- `abits <address bits>;`
- `width <width>;`
- `widths <width 1> <width 2> ... <width n> <global|per_port>;`
- `byte <width>;`
- `cost <cost>;`
- `widthscale [<factor>];`
- `resource <name> <count>;`
- `init <none|zero|any|no_undef>;`
- `style "<name 1>" "<name 2>" "<name 3>" ...;`
- `prune_rom;`

### RAM dimensions

The memory dimensions are described by `abits` and `width` or `widths` properties.

For a simple memory cell with a fixed width, use `abits` and `width` like this:

    abits 4;
    width 4;

This will result in a `2**abits × width` memory cell.

Multiple-width memories are also possible, and use the `widths` property instead.
The rules for multiple-width memories are:

- the widths are given in `widths` property in increasing order
- the value in the `abits` property corresponds to the most narrow width
- every width in the list needs to be greater than or equal to twice
  the previous width (ie. `1 2 4 9 18` is valid, `1 2 4 7 14` is not)
- it is assumed that, for every width in progression, the word in memory
  is made of two smaller words, plus optionally some extra bits (eg. in the above
  list, the 9-bit word is made of two 4-bit words and 1 extra bit), and thus
  each sequential width in the list corresponds to one fewer usable address bit
- all addresses connected to memory ports are always `abits` bits wide, with const
  zero wired to the unused bits corresponding to wide ports

When multiple widths are specified, they can be `per_port` or `global`.
For the `global` version, the pass has to pick one width for the whole cell,
and it is set on the resulting cell as the `WIDTH` parameter.  For the `per_port`
version, the selection is made on per-port basis, and passed using `PORT_*_WIDTH`
parameters.  When the mode is `per_port`, the width selection can be fine-tuned
with the port `width` property.

Specifying dimensions is mandatory.


### Byte width

If the memory cell has per-byte write enables, the `byte` property can be used
to define the byte size (ie. how many data bits correspond to one write enable
bit).

The property is optional.  If not used, it is assumed that there is a single
write enable signal for each writable port.

The rules for this property are as follows:

- for every available width, the width needs to be a multiple of the byte size,
  or the byte size needs to be larger than the width
- if the byte size is larger than the width, the byte enable signel is assumed
  to be one bit wide and cover the whole port
- otherwise, the byte enable signal has one bit for every `byte` bits of the
  data port

The exact kind of byte enable signal is determined by the presence or absence
of the per-port `wrbe_separate` property.


### Cost properties

The `cost` property is used to estimate the cost of using a given mapping.
This is the cost of using one cell, and will be scaled as appropriate if
the mapping requires multiple cells.

If the `widthscale` property is specified, the mapping is assumed to be flexible,
with cost scaling with the percentage of data width actually used.  The value
of the `widthscale` property is how much of the cost is scalable as such.
If the value is omitted, all of the cost is assumed to scale.
Eg. for the following properties:

    width 14;
    cost 8;
    widthscale 7;

The cost of a given cell will be assumed to be `(8 - 7) + 7 * (used_bits / 14)`.

If `widthscale` is used, The pass will attach a `BITS_USED` parameter to mapped
calls, with a bitmask of which data bits of the memory are actually in use.
The parameter width will be the widest width in the `widths` property, and
the bit correspondence is defined accordingly.

The `cost` property is mandatory.


### `init` property

This property describes the state of the memory at initialization time.  Can have
one of the following values:

- `none`: the memory contents are unpredictable, memories requiring any sort
  of initialization will not be mapped to this cell
- `zero`: the memory contents are zero, memories can be mapped to this cell iff
  their initialization value is entirely zero or undef
- `any`: the memory contents can be arbitrarily selected, and the initialization
  will be passes as the `INIT` parameter to the mapped cell
- `no_undef`: like `any`, but only 0 and 1 bit values are supported (the pass will
  convert any x bits to 0)

The `INIT` parameter is always constructed as a concatenation of words corresponding
to the widest available `widths` setting, so that all available memory cell bits
are covered.

This property is optional and assumed to be `none` when not present.


### `style` property

Provides a name (or names) for this definition that can be passed to the `ram_style`
or similar attribute to manually select it.  Optional and can be used multiple times.


### `prune_rom` property

Specifying this property disqualifies the definition from consideration for source
memories that have no write ports (ie. ROMs).  Use this on definitions that have
an obviously superior read-only alternative (eg. LUTRAMs) to make the pass skip
them over quickly.


## Port definition blocks

The syntax for a port group definition is:

    port <ar|sr|sw|arsw|srsw> "NAME 1" "NAME 2" ... {
        <port properties>
    }

A port group definition defines a group of ports with identical properties.
There are as many ports in a group as there are names given.

Ports come in 5 kinds:

- `ar`: asynchronous read port
- `sr`: synchronous read port
- `sw`: synchronous write port
- `arsw`: simultanous synchronous write + asynchronous read with common address (commonly found in LUT RAMs)
- `srsw`: synchronous write + synchronous read with common address

The port properties available are:

- `width <tied|mix>;`
- `width <width 1> <width 2> ...;`
- `width <tied|mix> <width 1> <width 2> ...;`
- `width rd <width 1> <width 2> ... wr <width 1> <width 2> ...;`
- `clock <posedge|negedge|anyedge> ["SHARED_NAME"];`
- `clken;`
- `rden;`
- `wrbe_separate;`
- `rdwr <undefined|no_change|new|old|new_only>;`
- `rdinit <none|zero|any|no_undef>;`
- `rdarst <none|zero|any|no_undef|init>;`
- `rdsrst <none|zero|any|no_undef|init> <ungated|gatec_clken|gated_rden> [block_wr];`
- `wrprio "NAME" "NAME" ...;`
- `wrtrans <"NAME"|all> <old|new>;`
- `optional;`
- `optional_rw;`

The base signals connected to the mapped cell for ports are:

- `PORT_<name>_ADDR`: the address
- `PORT_<name>_WR_DATA`: the write data (for `sw`/`arsw`/`srsw` ports only)
- `PORT_<name>_RD_DATA`: the read data (for `ar`/`sr`/`arsw`/`srsw` ports only)
- `PORT_<name>_WR_EN`: the write enable or enables (for `sw`/`arsw`/`srsw` ports only)

The address is always `abits` wide.  If a non-narrowest width is used, the appropriate low
bits will be tied to 0.


### Port `width` prooperty

If the RAM has `per_port` widths, the available width selection can be further described
on per-port basis, by using one of the following properties:

- `width tied;`: any width from the master `widths` list is acceptable, and
  (for read+write ports) the read and write width has to be the same
- `width tied <width 1> <width 2> ...;`: like above, but limits the width
  selection to the given list; the list has to be a contiguous sublist of the
  master `widths` list
- `width <width 1> <width 2> ...;`: alias for the above, to be used for read-only
  or write-only ports
- `width mix;`: any width from the master `widths` list is acceptable, and
  read width can be different than write width (only usable for read+write ports)
- `width mix <width 1> <width 2> ...;`: like above, but limits the width
  selection to the given list; the list has to be a contiguous sublist of the
  master `widths` list
- `width rd <width 1> <width 2> ... wr <width 1> <width 2> ...;`: like above,
  but the limitted selection can be different for read and write widths

If `per_port` widths are in use and this property is not specified, `width tied;` is assumed.

The parameters attached to the cell in `per_port` widths mode are:

- `PORT_<name>_WIDTH`: the selected width (for `tied` ports)
- `PORT_<name>_RD_WIDTH`: the selected read width (for `mix` ports)
- `PORT_<name>_WR_WIDTH`: the selected write width (for `mix` ports)


### `clock` property

The `clock` property is used with synchronous ports (and synchronous ports only).
It is mandatory for them and describes the clock polarity and clock sharing.
`anyedge` means that both polarities are supported.

If a shared clock name is provided, the port is assumed to have a shared clock signal
with all other ports using the same shared name.  Otherwise, the port is assumed to
have its own clock signal.

The port clock is always provided on the memory cell as `PORT_<name>_CLK` signal
(even if it is also shared).  Shared clocks are also provided as `CLK_<shared_name>`
signals.

For `anyedge` clocks, the cell gets a `PORT_<name>_CLKPOL` parameter that is set
to 1 for `posedge` clocks and 0 for `negedge` clocks.  If the clock is shared,
the same information will also be provided as `CLK_<shared_name>_POL` parameter.


### `clken` and `rden`

The `clken` property, if present, means that the port has a clock enable signal
gating both reads and writes.  Such signal will be provided to the mapped cell
as `PORT_<name>_CLK_EN`.  It is only applicable to synchronous ports.

The `rden` property, if present, means that the port has a read clock enable signal.
Such signal will be provided to the mapped cell as `PORT_<name>_RD_EN`.  It is only
applicable to synchronous read ports (`sr` and `srsw`).

For `sr` ports, both of these options are effectively equivalent.


### `wrbe_separate` and the write enables

The `wrbe_separate` property specifies that the write byte enables are provided
as a separate signal from the main write enable.  It can only be used when the
RAM-level `byte` property is also specified.

The rules are as follows:

If no `byte` is specified:

- `wrbe_separate` is not allowed
- `PORT_<name>_WR_EN` signal is single bit

If `byte` is specified, but `wrbe_separate` is not:

- `PORT_<name>_WR_EN` signal has one bit for every data byte
- `PORT_<name>_WR_EN_WIDTH` parameter is the width of the above (only present for multiple-width cells)

If `byte` is specified and `wrbe_separate` is present:

- `PORT_<name>_WR_EN` signal is single bit
- `PORT_<name>_WR_BE` signal has one bit for every data byte
- `PORT_<name>_WR_BE_WIDTH` parameter is the width of the above (only present for multiple-width cells)
- a given byte is written iff all of `CLK_EN` (if present), `WR_EN`, and the corresponding `WR_BE` bit are one

This property can only be used on write ports.


### `rdwr` property

This property is allowed only on `srsw` ports and describes read-write interactions.

The possible values are:

- `no_change`: if write is being performed (any bit of `WR_EN` is set),
  reading is not performed and the `RD_DATA` keeps its old value
- `undefined`: all `RD_DATA` bits corresponding to enabled `WR_DATA` bits
  have undefined value, remaining bits read from memory
- `old`: all `RD_DATA` bits get the previous value in memory
- `new`: all `RD_DATA` bits get the new value in memory (transparent write)
- `new_only`: all `RD_DATA` bits corresponding to enabled `WR_DATA` bits
  get the new value, all others are undefined

If this property is not found on an `srsw` port, `undefined` is assumed.


### Read data initial value and resets

The `rdinit`, `rdarst`, and `rdsrst` are applicable only to synchronous read
ports.

`rdinit` describes the initial value of the read port data, and can be set to
one of the following:

- `none`: initial data is indeterminate
- `zero`: initial data is all-0
- `any`: initial data is arbitrarily configurable, and the selected value
  will be attached to the cell as `PORT_<name>_RD_INIT_VALUE` parameter
- `no_undef`: like `any`, but only 0 and 1 bits are allowed

`rdarst` and `rdsrst` describe the asynchronous and synchronous reset capabilities.
The values are similar to `rdinit`:

- `none`: no reset
- `zero`: reset to all-0 data
- `any`: reset to arbitrary value, the selected value
  will be attached to the cell as `PORT_<name>_RD_ARST_VALUE` or
  `PORT_<name>_RD_SRST_VALUE` parameter
- `no_undef`: like `any`, but only 0 and 1 bits are allowed
- `init`: reset to the initial value, as specified by `rdinit` (which must be `any`
  or `no_undef` itself)

If the capability is anything other than `none`, the reset signal
will be provided as `PORT_<name>_RD_ARST` or `PORT_<name>_RD_SRST`.

For `rdsrst`, the priority must be additionally specified, as one of:

- `ungated`: `RD_SRST` has priority over both `CLK_EN` and `RD_EN` (if present)
- `gated_clken`: `CLK_EN` has priority over `RD_SRST`; `RD_SRST` has priority over `RD_EN` if present
- `gated_rden`: `RD_EN` and `CLK_EN` (if present) both have priority over `RD_SRST`

Also, `rdsrst` can optionally have `block_wr` specified, which means that sync reset
cannot be performed in the same cycle as a write.

If not provided, `none` is assumed for all three properties.


### Write priority

The `wrprio` property is only allowed on write ports and defines a priority relationship
between port — when `wrprio "B";` is used in definition of port `"A"`, and both ports
simultanously write to the same memory cell, the value written by port `"A"` will have
precedence.

This property is optional, and can be used multiple times as necessary.  If no relationship
is described for a pair of write ports, no priority will be assumed.


### Write transparency

The `wrtrans` property is only allowed on write ports and defines behavior when
another synchronous read port reads from the memory cell at the same time as the
given port writes it.  The values are:

- `old`: the read port will get the old value of the cell
- `new`: the read port will get the new value of the cell

This property is optional, and can be used multiple times as necessary.  If no relationship
is described for a pair of ports, the value read is assumed to be indeterminate.

Note that this property is not used to describe the read value on the port itself for `srsw`
ports — for that purpose, the `rdwr` property is used instead.


### Optional ports

The `optional;` property will make the pass attach a `PORT_<name>_USED` parameter
with a boolean value specifying whether a given port was meaningfully used in
mapping a given cell.  Likewise, `optional_rw;` will attach `PORT_<name>_RD_USED`
and `PORT_<name>_WR_USED` the specify whether the read / write part in particular
was used.  These can be useful if the mapping has some meaningful optimization
to apply for unused ports, but doesn't otherwise influence the selection process.


## Options

For highly configurable cells, multiple variants may be described in one cell description.
All properties and port definitions within a RAM or port definition can be put inside
an `option` block as follows:

    option "NAME" <value> {
        <properties, ports, ...>
    }

The value and name of an option are arbitrary, and the selected option value
will be provided to the cell as `OPTION_<name>` parameter.  Values can be
strings or integers.


Likewise, for per-port options, a `portoption` block can be used:

    portoption "NAME" <value> {
        <properties, ...>
    }

These options will be provided as `PORT_<pname>_OPTION_<oname>` parameters.

The library parser will simply expand the RAM definition for every possible combination
of option values mentioned in the RAM body, and likewise for port definitions.
This can lead to a combinatorial explosion.

If some option values cannot be used together, a `forbid` pseudo-property can be used
to discard a given combination, eg:

    option "ABC" 1 {
        portoption "DEF" "GHI" {
            forbid;
        }
    }

will disallow combining the RAM option `ABC = 2` with port option `DEF = "GHI"`.


## Ifdefs

To allow reusing a library for multiple FPGA families with slighly differing
capabilities, `ifdef` (and `ifndef`) blocks are provided:

    ifdef IS_FANCY_FPGA_WITH_CONFIGURABLE_ASYNC_RESET {
        rdarst any;
    } else {
        rdarst zero;
    }

Such blocks can be enabled by passing the `-D` option to the pass.
