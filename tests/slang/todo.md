# Document the differences

## Top Attribute Inferred

Slang infers top, and adds a `(* top *)` attribute to modules without parents, read verilog does not do this, and `hierarchy` cannot handle that, see logs from typedef_struct_port.ys for an example:

```
2. Executing HIERARCHY pass (managing design hierarchy).
Attribute `top' found on module `top'. Setting top module to top.
Attribute `top' found on module `test_parser'. Setting top module to test_parser.
```

### Fixes

The fix is to add a `setattr -mod -unset top` before hierarchy in the script.

Tests affected:
- typedef_struct_port.ys
- cellarray_array_connections.ys
- for_decl_shadow.ys

## Inserted Buffers

Slang seems to emit buffers when read_verilog would not. This messes up existing flows that do not expect buffers: `proc -> opt_expr`. 

### Fixes

The fix is adding `opt_clean` before `opt_expr` in the script. This can & probably should be called by read_slang instead. 

At least abstract_init.ys is affected and I've seen a few others

## Undefined Modules

While read_verilog can handle undefined modules and elaborate those later, `read_slang` required they be instantiated before elaboration. e.g. where `read_verilog` handles this `read_slang` fails

```sh
read_slang --no-proc --std latest <<EOT
module top (CLK, E, Q, Q_EN);
	input CLK;
	input E;
	output reg Q;
	output reg Q_EN;
	half_clock uut (CLK, Q, 1'b0);
	half_clock_en uut_en (CLK, E, Q_EN, 1'b0);
endmodule
EOT
opt_clean
proc
design -import half_clock
design -import half_clock_en
hierarchy -check -top top
```

### Fixes

1. Move `design -import *` before `read_slang`
2. Add a flag to `read_slang` that reads a module as a blackbox, and can instantiate it later
	3. This likely needs to be a part of a bigger refactoring to add deferred elab with slang

## Slang emits $aldff cells by default

`read_slang` seems to emit `$aldff` cells by default. A lot of tests expect dff cells, I don't know if `$aldff` are rejected by some passes, needs more searching

### Fixes

Running `opt_dff` after `opt_clean` seems to fix the issue.

## Z trit

read_slang implicitly converts `z` trits to `x` trits which have different semantics.

### Fix

I don't think this can be fixed inside yosys, this seems likely to need fixes in sv-elab or slang itself to preserve those

## $initstate

This behavior should probably be fixed? 

```systemverilog
`ifdef READ_SLANG
    reg initial_state = 1'b1;

    always @(posedge clock)
        initial_state <= 1'b0;

    always @*
        assume (reset == initial_state);
`elsif YOSYS
    always @*
        assume (reset == $initstate);
`endif
```
