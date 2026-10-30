# Slang Taxonomy of issues

## Real Blockers

- Several passes need deferred parameter instantiation, and those don't work with slang, like `techmap`, with lib read by slang
	- [tests/slang/fpga/xilinx/dsp_abc9.ys], even when it is forward declared, it still has the parameter issue
- Blackbox unknown modules / blackbox leave params blank. When techmap is used, some tests use a primitive slang cannot see and can't instantiate until later. At least letting blackboxes exist unconcretized might be a workaround
		- [tests/slang/asic/techmap/cellname.ys]
- Sometimes a user wants to declare a primitive cell in a verilog file, those usually come prefixed with a $, which slang doesn't accept as valid verilog syntax
	- [tests/slang/fpga/xilinx/xilinx_srl.ys]
- [tests/slang/asic/techmap/iopadmap.ys]: ERROR: Module `\ibuf' referenced in module `\a' in cell `$iopadmap$a.i' is not part of the design.
	- Seems like a Real issue, I can't find a simple fix, the ibuf module is fully deleted from the design
- Slang seems to alphebetize the port order which disagrees with how other frontend expect it
	- [tests/slang/basic/verific/port_bus_order.ys]
- Slang doesn't preserve Z bits
	- [tests/slang/basic/opt/opt_dff_dffmux.ys]
- Slang cannot handle multiple async loads
	- [tests/slang/asic/abc_new/openroad/dffrsn_equiv.ys]
- Slang doesn't handle +/... paths
	- [tests/slang/fpga/gowin/init.ys]

## Easy Blockers

- Some tests declare a blackbox of a module with specify and then later overwrite it with a liberty file, and overwriting blackboxes isn's supported in read_slang
	- [tests/slang/asic/abc_new/librelane/abc_librelane.ys.in]
- Blackboxes don't preserve specify info
	- [tests/slang/asic/techmap/xaiger2-keep-box.ys]
- Specify doesn't work with params and need to use specparam, I don't think it works at this moment
	- [tests/slang/fpga/xilinx/bug1605.ys]
- Slang has a lot of attribute issues (missing attributes)
	- [tests/slang/basic/verific/enum_values.ys] - missing wiretype attribute
	- [tests/slang/basic/verilog/sbvector.ys] - missing single_bit_vector attribute
	- [tests/slang/basic/various/check_nolatches.ys] - missing always_latch attribute
	- [tests/slang/basic/various/json_netnames_signed.ys] - missing signed type 
- Slang seems to have a lot of structural differences between how it & read_verilog instantiate latches, slang adds a lot more muxes 
	- [tests/slang/basic/proc/yosys_latch.ys]
- Slang doesn't respect the (* mem2reg *) attribute? Unsure if this can be applied later
	- [tests/slang/basic/various/mem2reg.ys]
- Slang doesn't properly emit diagnostics for latches when later running proc
	- [tests/slang/basic/proc/proc_latches.ys]
- Slang seems to have the wrong associativity for exp
	- [tests/slang/basic/opt/pow_assoc.ys]
- Some formal tools use `$initstate` to model reset behavior among other things and `$initstate` isn't supported by read_slang
- Read Slang infers top attributes and sets it for each top module, and hierarchy only handles one or no top modules, should be a yosys fix
	- [tests/slang/basic/svtypes/typedef_struct_port.ys]
- Formal cells lack `keep`: add `setattr -set keep 1 t:$check` before `chformal -lower`.
  - [tests/slang/basic/opt/opt_merge_properties.ys]

## Workarounds

- Slang flattens modules by default, add `--best-effort-hierarchy`.
	- [basic/various/blackbox_wb.ys]
- When parameters need to be changed, that needs to be done in the read_slang command itself
	- [tests/slang/fpga/analogdevices/blockram.ys]
- Slang adds a lot of Buffers: use `opt_clean`, can affect `opt_expr` if cleaning is not done first, can see better when adding `--no-proc` flag
  - [tests/slang/basic/various/abstract_state.ys]
- Slang emits `$aldff` cells, need `opt_dff` to run.
  - [tests/slang/basic/various/rename_wire_move_to_cell.ys]
- Arithmetic cells are sized abnormally, add a `wreduce` option. Can probably add to default passes called by slang
	- [tests/slang/basic/opt/opt_expr_alu.ys]
- read_verilog automatically treats empty modules as blackboxes, slang needs `--empty-blackboxes`
	- [tests/slang/asic/techmap/clkbufmap.ys]
- Slang eagerly elaborates so calling hierarchy seems to not do much, some tests pass when its removed
	- [tests/slang/asic/techmap/clkbufmap.ys]

## Non-Issues

- `--noopt`
- Tests to do with the specific names of wires, slang names differently but these don't really seem to be about slang, and the failures aren't  blocking real use cases

## No Idea

- [basic/various/box_derive.ys]
	- apparently Martin wrote this, he would be good to ask
- [fpga/xilinx/dsp_cascade.ys]
- [fpga/gatemate/fsm.ys]
- [basic/various/submod.ys]
- [basic/various/dynamic_part_select.ys]

# Detailed Taxonomy

## Real Blockers

### Deferred Parameter Instantiation

- basic/verific/blackbox_empty.ys: <inlined>:2: ERROR: parameter 'PATH' does not exist in 'TEST_CELL' [-Wundefined-param-override]
	- Fails due to no deferred parameter evaluation
	- Succeeds if the two slang calls are merged

- basic/various/bug3462.ys: <inlined>:4: ERROR: parameter 'd' does not exist in 'sub' [-Wundefined-param-override]
	- same as above, succeeds when together but that doesn't seem to be what its testing.

- basic/various/hierarchy_reprocess_abc9.ys: ERROR: Module `bb' is used with parameters but is not parametric!
	- blocked by deferred parameter evaluation

### Unknown Modules

#### Techmap

Seems ultimately blocked by both deferred param instantiation as well as blackboxes

- asic/techmap/techmap_chtype.ys: <inlined>:15: ERROR: unknown module '_TECHMAP_PLACEHOLDER_'
	- Blocked by not blackboxing unknown modules

- asic/techmap/cellname.ys: <inlined>:4: ERROR: unknown module 'namedsub'
	- Blocked by techmap trying to reinstantiate with different params

- asic/techmap/techmap_replace.ys: <inlined>:2: ERROR: unknown module 'foobar'
	- also: <inlined>:3: ERROR: expected ';' wire _TECHMAP_REPLACE_.asdf = i ;

#### Primitive Libs

These seem likely to be blocked by deferred parameter instantiation

- fpga/xilinx/dsp_abc9.ys: <inlined>:2: ERROR: unknown module 'DSP48E1'

- fpga/xilinx/abc9_dff.ys: <inlined>:2: ERROR: unknown module 'FDRE'

- fpga/xilinx/xilinx_dsp.ys: <inlined>:2: ERROR: unknown module 'DSP48E1'

- fpga/ice40/ice40_wrapcarry.ys: <inlined>:2: ERROR: unknown module 'SB_CARRY'

- fpga/ice40/ice40_opt.ys: <inlined>:3: ERROR: unknown module '$__ICE40_CARRY_WRAPPER'
	- Blocked by missing icells, even when read_verilog is used for icells, slang fails to reinstantiate verilog model with new params

- fpga/xilinx/bug3670.ys: bug3670.v:4: ERROR: unknown module 'RAMB36E1'
	- blocked by not accepting +/path
	- if raw path is provided, it still fails due to parameters in specify blocks

### Idents with $

- asic/techmap/dfflibmap_formal.ys: <inlined>:4: ERROR: expected member

- asic/techmap/dlatchlibmap_formal.ys: <inlined>:4: ERROR: expected member

- fpga/xilinx/xilinx_srl_enable.ys: <inlined>:9: ERROR: expected identifier

- fpga/xilinx/xilinx_srl.ys: xilinx_srl.v:29: ERROR: expected identifier

### Blackboxes

- asic/techmap/iopadmap.ys: ERROR: Module `\ibuf' referenced in module `\a' in cell `$iopadmap$a.i' is not part of the design.
	- Seems like a Real issue, I can't find a simple fix, the ibuf module is fully deleted from the design

### Port Order

- basic/verific/port_bus_order.ys: ERROR: Shell command returned error code 256.
	- Real Issue
	- alphabetizes internally

### Z -> X

- basic/opt/opt_dff_dffmux.ys: ERROR: Found 1 unproven $equiv cells in 'equiv_status -assert'.

- fpga/machxo2/tribuf.ys: ERROR: Found 1 unproven $equiv cells in 'equiv_status -assert'.

### Multiple Asynchronous Loads

- asic/abc_new/openroad/dffrsn_equiv.ys: <inlined>:6: ERROR: multiple asynchronous loads unsupported

- asic/abc_new/openroad/remap_netlist.ys: cells_sim.v:33: ERROR: multiple asynchronous loads unsupported

- asic/liberty/read_liberty.ys: retention.lib.verilogsim:14: ERROR: multiple asynchronous loads unsupported

### +/ Paths

- basic/verific/blackbox_ql.ys: ERROR: '+/quicklogic/qlf_k6n10f/dsp_sim.v': No such file or directory

- fpga/gowin/init.ys: ERROR: unknown command line argument '+/gowin/cells_sim.v'

## Easy Blockers

### Cannot Overwrite Blackboxed Modules

- asic/abc_new/librelane/abc_librelane_area_0.ys: ERROR: Attempted to add new module named '\AND2', but a module by that name already exists
	- abc_librelane_area_{1,2,3}.ys: same issue
	- Param changes moved into read_slang, now fails because read_slang doesn't override blackboxes

- asic/abc_new/librelane/abc_librelane_delay_0.ys: ERROR: Attempted to add new module named '\AND2', but a module by that name already exists
	- abc_librelane_delay_{1,2,3}.ys: same issue

- asic/abc_new/scopeinfo.ys: ERROR: Attempted to add new module named '\AND2', but a module by that name already exists

- asic/abc_new/whitebox_equiv.ys: ERROR: Attempted to add new module named '\AND2', but a module by that name already exists

- asic/abc_new/openroad/cm_cases.ys: ERROR: Attempted to add new module named '\AND2', but a module by that name already exists

### Specify / Timing

- asic/techmap/xaiger2-keep-box.ys: ERROR: Module 'box' with (* abc9_box *) has no timing (and thus no connectivity) information.

- asic/techmap/xaiger2-5169.ys: ERROR: Module 'CC_MX4' with (* abc9_box *) has no timing (and thus no connectivity) information.

- fpga/xilinx/bug1605.ys: ../../../../techlibs/xilinx/cells_sim.v:509: ERROR: cannot refer to 'IS_C_INVERTED' in state-dependent path condition expression; only locally defined nets and variables are allowed

- fpga/ecp5/abc9_inout_pad_input.ys: ../../../../techlibs/lattice/common_sim.vh:304: ERROR: cannot refer to 'SRMODE' in state-dependent path condition expression; only locally defined nets and variables are allowed

### Keywords

- asic/techmap/bug2972.ys: <inlined>:2: ERROR: expected identifier
	- Uses `do` as name
	- otherwise uses specify in blackbox, still broken

### Missing Attributes

- basic/verific/enum_values.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: top/state a:wiretype=\state_t %i
	- basic fix, missing wiretype attribute

- basic/verilog/sbvector.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: w:i1 a:single_bit_vector %i
	- basic fix, missing single_bit_vector attribute

- basic/various/check_nolatches.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: t:$dlatch a:always_latch %i
	- basic fix, missing always_latch attribute

- basic/various/json_netnames_signed.ys: ERROR: Shell command returned error code 256.
	- basic fix, missing signed attribute on some wires
	- use rtlil?

### Latch Structure

- basic/proc/yosys_latch.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 2: t:$adlatch
	- probably a real issue? maybe basic, maybe workaround. latches have a pretty different topology than read_verilog suggests, can this be simplified in the frontend? should it?

- fpga/quicklogic/qlf_k6n10f/latches.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: t:latchnsre
	- Seems to be likely to be the same latch representation issue

### mem2reg

- basic/various/mem2reg.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: m:data1 a:src=<inlined>:4.43-4.48 %i
	- (* keep *) doesnt seem to be respected
	- neither does (* mem2reg *)
	- maybe basic issue, idk how important it is though

### Diagnostics

- basic/proc/proc_latches.ys: ERROR: Expected warning pattern 'Latch inferred for signal' not found !

### Exponentiation Associativity

- basic/opt/pow_assoc.ys: ERROR: Found 2 unproven $equiv cells in 'equiv_status -assert'.
	- I think read_verilog and read_slang disagree on exponentiation associativity
	- read_verilog is probably correct
	- Real Issue

## Workarounds

### Parameter Overrides

- fpga/analogdevices/blockram.ys: ERROR: Module `sync_ram_sdp' not found!
	- need to manually instantiate params and specify top manually

- fpga/ecp5/memories.ys: ERROR: Module `sync_ram_sdp' not found!

- fpga/ice40/memories.ys: ERROR: Module `sync_ram_sdp' not found!

### Arithmetic Widths

- basic/peepopt/muldiv_c.ys: ERROR: Assertion failed: selection is not empty: t:$div
	- kindof workaround - wreduce
	- works for some not others, need more effort, probably a yosys issue, the rest are probably basic, one peepopt succeeds where it shouldn't?

- basic/opt/opt_expr_alu.ys: ERROR: Assertion failed: selection contains 0 elements instead of the asserted 1: t:$pos
	- workaround wreduce

## No Idea

- basic/various/box_derive.ys: <inlined>:2: ERROR: use of undeclared identifier 'X'
	- ask martin

- fpga/xilinx/dsp_cascade.ys: ERROR: Assertion failed: selection contains 10 elements instead of the asserted 5: t:FDRE

- fpga/gatemate/fsm.ys: ERROR: Assertion failed: selection contains 2 elements instead of the asserted 0: t:CC_LUT2

- basic/various/submod.ys: Warning: Wire top.q has an unprocessed 'init' attribute., ERROR: Found 1 problems in 'check -assert'.


- basic/various/dynamic_part_select.ys: ERROR: Called with -verify and proof did fail!
