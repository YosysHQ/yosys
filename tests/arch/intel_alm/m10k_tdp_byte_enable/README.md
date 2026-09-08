# Opt-in byte-masked true-dual-port Cyclone V M10K

Use `(* ram_style="m10k_tdp_byte" *)` for two synchronous read/write ports
with independent two-lane write masks. [top.v](top.v) is the supported
inference idiom: on an enabled edge, either write the selected lanes or
read the word. The RTL output holds during writes and while disabled.
Yosys adds output-hold logic around the M10K to preserve that behavior.
Both independent and shared positive-edge clocks are supported.

The mapper uses one physical 512x20 TDP M10K for a 512x20 array (two 10-bit
lanes) or a 512x16 array (two 8-bit bytes). Each 8-bit byte occupies the
low eight bits of its physical 10-bit lane, including initialization data;
the two padding bits are unused (synthesis may mark them as don’t-care).
Mask bit 0 controls the lower lane and mask bit 1 the upper lane on each port.

This style is separate from `m10k_tdp`, whose whole-word 1024x10 and 512x20
geometries and write-through behavior remain unchanged. Untagged memories
also retain their existing mapping flow. Build and install the executable
and techlibs together; matching nextpnr Mistral byte-mask support is required.

The style opts into `memory_dff -no-rw-check` for cross-port collisions.
Applications must exclude same-address cross-port accesses involving a
write, including the hardware timing window around independent clock edges.
No cross-port write priority or collision result is promised.

## Primitive contract

`MISTRAL_M10K_TDP` gains `CFG_BYTE_ENABLE` (default 0) and active-high
`A1BE[1:0]` / `B1BE[1:0]`. Byte mode requires `CFG_ABITS=9`, `CFG_DBITS=20`.
Each lane writes only when that port's clock enable, master write enable
(`A1WE` / `B1WE`) and lane mask are all asserted. Disabled lanes retain
their stored contents and later reads return the complete stored word.

During a primitive write cycle, enabled output lanes return NEW_DATA;
disabled output lanes are unspecified (`NEW_DATA_NO_NBE_READ`), including
both lanes when the master write enable is asserted with mask zero.
Do not infer an old/new merged output word from the preserved storage.
An enabled non-write reads the complete word, regardless of byte mask;
a disabled port holds its output and does not write.
When `CFG_BYTE_ENABLE=0`, the mask inputs are ignored.

The library uses `wrbe_separate` and `rdwr new_only`. Its read port must
exclude writes for byte-mask inference: the generic memory representation
otherwise requires preserving unmodified output lanes and forces uniform
writes. A write-through RTL idiom with `'x` on disabled output lanes is
not the supported inference pattern. Instantiate the primitive explicitly
if its native write-cycle output behavior is needed without emulation.

## Host regression

```sh
python3 tests/arch/intel_alm/m10k_tdp_byte_enable/regression.py \
  --yosys /path/to/install/bin/yosys --output /tmp/m10k-tdp-byte-proof
```

Six cases cover logical 16- and 20-bit widths, independent/shared clocks,
and constant mask bits on both ports. Every case checks full-depth inference
of exactly one TDP primitive, physical dimensions, byte mode, clock wiring,
and all 512 initialized payload words. It then restricts both addresses to
the first and last four-word pages for 12-step SAT equivalence of the RTL
and the expanded physical model. Clocks, enables, masks, low address bits
and both write-data inputs remain symbolic. This checks output hold,
masked storage writes, and subsequent complete-word reads. Each case also
checks one-cell inference through the public synthesis flow without the
preparatory passes used to construct the equivalence comparison.

A separate 12-step [primitive check](primitive.v) compares the explicit
physical primitive against two independent reference byte banks. It checks
enabled-lane NEW_DATA on writes, output hold while disabled, and later
complete reads after arbitrary masked writes. Disabled write-output lanes
are excluded from comparison; they are not asserted to retain old data.

The formal fixture excludes simultaneous enabled same-address access
involving a write, a stronger exclusion than edge-only collision checks.
Non-memory initial state is zero for bounded comparison; explicit memory
INIT is preserved. These are host-only bounded window checks, not an
unbounded full-memory proof or hardware acceptance.
