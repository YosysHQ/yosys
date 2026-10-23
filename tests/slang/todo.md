# Document the differences

## Top Attribute Inferred

Slang infers top, and adds a `(* top *)` attribute to modules without parents, read verilog does not do this, and `hierarchy` cannot handle that, see logs from typedef_struct_port.ys for an example:

```
2. Executing HIERARCHY pass (managing design hierarchy).
Attribute `top' found on module `top'. Setting top module to top.
Attribute `top' found on module `test_parser'. Setting top module to test_parser.
```

The fix is to add a `setattr -mod -unset top` before hierarchy in the script.

Tests affected:
- typedef_struct_port.ys
- cellarray_array_connections.ys
- for_decl_shadow.ys

## Inserted Buffers

Slang seems to emit buffers when read_verilog would not. This messes up existing flows that do not expect buffers: `proc -> opt_expr`. 

The fix is adding `opt_clean` before `opt_expr` in the script. This can & probably should be called by read_slang instead. 

At least abstract_init.ys is affected and I've seen a few others

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
