# Changes Needed for Slang

- `--icells`
- `--defer`

## Lower priority

- `$initstate` is only supported by read_verilog and not read_slang
- `--mem2reg` / `--nomem2reg`
- `--pwires`
- `--overwrite` / `--no-overwrite`

# Changes Implemented for Slang

- Only in a local branch for sv_elab, need to clean up that branch and make a few PRs into sv_elab, but those are probably blocked by rewriter

- `--specify`
	- Unsure if 100% correct, tried to copy / merge read_verilog parser into sv_elab
- `--noopt`

# Passing Tests with Changes Needed to Tests

- Inferred top attributes: unset `top` before hierarchy.
  - basic/svtypes/typedef_struct_port.ys
  - basic/various/cellarray_array_connections.ys
  - basic/verilog/for_decl_shadow.ys

- Default flattening: add `--best-effort-hierarchy`.
  - basic/various/json_scopeinfo.ys
  - basic/various/blackbox_wb.ys

- Default memory inference: add `--no-implicit-memories`.
  - basic/opt/opt_dff_eqbits.ys

- Slang adds a lot of Buffers: use `opt_clean`, can affect `opt_expr` if cleaning is not done first
  - basic/various/abstract_init.ys
  - basic/various/abstract_state.ys
  - basic/various/keep_hierarchy.ys

- Slang emits `$aldff` cells, need `opt_dff` to run.
  - basic/various/rename_wire_move_to_cell.ys

- Formal cells lack `keep`: add `setattr -set keep 1 t:$check` before `chformal -lower`.
  - basic/opt/opt_merge_properties.ys

# Remaining Slang failures

## Unknown Modules

- Definitions must be imported before `read_slang`, rather than afterward.
	- can usually be fixed in the test, but would be nice if it worked like read verilog, 
	- I assume it's blocked by the same thing as defer

### Techmap

- asic/techmap/techmap_chtype.ys: <inlined>:15: ERROR: unknown module '_TECHMAP_PLACEHOLDER_'
- asic/techmap/cellname.ys: <inlined>:4: ERROR: unknown module 'namedsub'
- asic/techmap/autopurge.ys: <inlined>:2: ERROR: unknown module 'foobar'
- asic/techmap/techmap_replace.ys: <inlined>:2: ERROR: unknown module 'foobar'

### Primitive Libs

- fpga/xilinx/dsp_abc9.ys: <inlined>:2: ERROR: unknown module 'DSP48E1'
- fpga/xilinx/abc9_dff.ys: <inlined>:2: ERROR: unknown module 'FDRE'
- fpga/xilinx/xilinx_dsp.ys: <inlined>:2: ERROR: unknown module 'DSP48E1'
- fpga/ice40/ice40_wrapcarry.ys: <inlined>:2: ERROR: unknown module 'SB_CARRY'
- fpga/ice40/ice40_opt.ys: <inlined>:3: ERROR: unknown module '$__ICE40_CARRY_WRAPPER'
- fpga/xilinx/bug3670.ys: bug3670.v:4: ERROR: unknown module 'RAMB36E1'

## Parameter Issues

- basic/verific/blackbox_empty.ys: <inlined>:2: ERROR: parameter 'PATH' does not exist in 'TEST_CELL' [-Wundefined-param-override]
- basic/various/bug3462.ys: <inlined>:4: ERROR: parameter 'd' does not exist in 'sub' [-Wundefined-param-override]

### Cannot reset Params

- asic/abc_new/librelane/abc_librelane_area_0.ys: ERROR: Module `spm' is used with parameters but is not parametric!
	- abc_librelane_area_{1,2,3}.ys: same issue
- asic/abc_new/librelane/abc_librelane_delay_0.ys: ERROR: Module `spm' is used with parameters but is not parametric!
	- abc_librelane_delay_{1,2,3}.ys: same issue
- basic/various/hierarchy_reprocess_abc9.ys: ERROR: Module `bb' is used with parameters but is not parametric!

## Syntax

### General / Unsure

- basic/various/rename_unescape.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: w:$e
- basic/various/struct_access.ys: struct_access.sv:24: ERROR: invalid member access for type 'logic[1:0]'

### Keyword

- asic/techmap/bug2972.ys: <inlined>:2: ERROR: expected identifier
	- Uses `do` as name

### Idents with $

- asic/techmap/dfflibmap_formal.ys: <inlined>:4: ERROR: expected member
- asic/techmap/dlatchlibmap_formal.ys: <inlined>:4: ERROR: expected member
- fpga/xilinx/xilinx_srl_enable.ys: <inlined>:9: ERROR: expected identifier
- fpga/xilinx/xilinx_srl.ys: xilinx_srl.v:29: ERROR: expected identifier

### Net initializers

- asic/techmap/cellmatch.ys: <inlined>:3: ERROR: only 'output' variable port declarations may have an initializer expression

### Procedural assignments to nets

- fpga/ecp5/rom.ys: rom.v:9: ERROR: cannot assign to a net within a procedural context
- fpga/ice40/rom.ys: rom.v:10: ERROR: cannot assign to a net within a procedural context
- fpga/ice40/spram.ys: spram.v:19: ERROR: cannot assign to a net within a procedural context

### Constant inout

- asic/techmap/bug2183.ys: <inlined>:5: ERROR: expression is not assignable

### rand keyword

- basic/various/rand_const.ys: rand_const.sv:2: ERROR: member not allowed in module declaration

### Attribute scope

- basic/various/box_derive.ys: <inlined>:2: ERROR: use of undeclared identifier 'X'

## Hierarchy

- asic/abc_new/paramod_equiv.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 2: top/t:$paramod*
- asic/techmap/iopadmap.ys: ERROR: Module `\ibuf' referenced in module `\a' in cell `$iopadmap$a.i' is not part of the design.
- asic/techmap/clkbufmap.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 3: top/t:clkbuf
- asic/techmap/module_not_derived.ys: ERROR: Assertion failed: selection is empty: t:mycell a:module_not_derived %i
- basic/opt/bug1793.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 2: sub/o:*
- basic/various/rename_scramble_name.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: c:$_*_
- asic/abc_new/scopeinfo.ys: ERROR: Attempted to add new module named '\AND2', but a module by that name already exists
- asic/abc_new/whitebox_equiv.ys: ERROR: Attempted to add new module named '\AND2', but a module by that name already exists
- asic/abc_new/openroad/cm_cases.ys: ERROR: Attempted to add new module named '\AND2', but a module by that name already exists
- fpga/analogdevices/blockram.ys: ERROR: Module `sync_ram_sdp' not found!
- fpga/ecp5/memories.ys: ERROR: Module `sync_ram_sdp' not found!
- fpga/ice40/memories.ys: ERROR: Module `sync_ram_sdp' not found!

## Metadata

- basic/verific/port_bus_order.ys: ERROR: Shell command returned error code 256.
- basic/verific/enum_values.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: top/state a:wiretype=\state_t %i
- basic/verilog/sbvector.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: w:i1 a:single_bit_vector %i
- basic/various/check_nolatches.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: t:$dlatch a:always_latch %i
- basic/various/json_netnames_signed.ys: ERROR: Shell command returned error code 256.
- basic/various/splitnets.ys: ERROR: Assertion failed: selection contains 1 elements instead of the asserted 0: w:a

## Optimization

- Arithmetic operands are extended to matching widths, unlike `read_verilog`, see basic/opt/opt_expr_alu.ys

- basic/peepopt/muldiv_c.ys: ERROR: Assertion failed: selection is not empty: t:$div
- basic/proc/yosys_latch.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 2: t:$adlatch
- basic/opt/opt_expr_alu.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: t:$pos
- basic/opt/opt_expr.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: t:$add r:A_WIDTH=5 r:B_WIDTH=4 r:Y_WIDTH=5 %i %i %i
- basic/various/mem2reg.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: m:data1 a:src=<inlined>:4.43-4.48 %i
- fpga/xilinx/dsp_cascade.ys: ERROR: Assertion failed: selection contains 10 elements instead of the asserted 5: t:FDRE
- fpga/gatemate/fsm.ys: ERROR: Assertion failed: selection contains 2 elements instead of the asserted 0: t:CC_LUT2
- fpga/quicklogic/qlf_k6n10f/latches.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: t:latchnsre

## Specify / Timing

- asic/techmap/xaiger2-keep-box.ys: ERROR: Module 'box' with (* abc9_box *) has no timing (and thus no connectivity) information.
- asic/techmap/xaiger2-5169.ys: ERROR: Module 'CC_MX4' with (* abc9_box *) has no timing (and thus no connectivity) information.
- fpga/xilinx/bug1605.ys: ../../../../techlibs/xilinx/cells_sim.v:509: ERROR: cannot refer to 'IS_C_INVERTED' in state-dependent path condition expression; only locally defined nets and variables are allowed
- fpga/ecp5/abc9_inout_pad_input.ys: ../../../../techlibs/lattice/common_sim.vh:304: ERROR: cannot refer to 'SRMODE' in state-dependent path condition expression; only locally defined nets and variables are allowed

## Diagnostics

- basic/proc/proc_latches.ys: ERROR: Expected warning pattern 'Latch inferred for signal' not found !

## Slang Semantics

- basic/various/submod.ys: Warning: Drivers conflicting with a constant 1'x driver: module input a[0], ERROR: Found 1 problems in 'check -assert'.
- basic/opt/opt_dff_dffmux.ys: ERROR: Found 1 unproven $equiv cells in 'equiv_status -assert'.
	- Issue with Z bits turning into X bits
- fpga/xilinx/priority_memory.ys: priority_memory.v:22: ERROR: non-blocking assignments unsupported in design initialization

### Multiple asynchronous loads

- asic/abc_new/openroad/dffrsn_equiv.ys: <inlined>:6: ERROR: multiple asynchronous loads unsupported
- asic/abc_new/openroad/remap_netlist.ys: cells_sim.v:33: ERROR: multiple asynchronous loads unsupported
- asic/liberty/read_liberty.ys: retention.lib.verilogsim:14: ERROR: multiple asynchronous loads unsupported

## SAT Errors

- basic/opt/pow_assoc.ys: ERROR: Found 2 unproven $equiv cells in 'equiv_status -assert'.
	- I think read_verilog and read_slang disagree on exponentiation associativity
- basic/various/dynamic_part_select.ys: ERROR: Called with -verify and proof did fail!
- fpga/machxo2/tribuf.ys: ERROR: Found 1 unproven $equiv cells in 'equiv_status -assert'.

## Test Inputs and Paths

### +/ paths

- basic/verific/blackbox_ql.ys: ERROR: '+/quicklogic/qlf_k6n10f/dsp_sim.v': No such file or directory
- fpga/gowin/init.ys: ERROR: unknown command line argument '+/gowin/cells_sim.v'
