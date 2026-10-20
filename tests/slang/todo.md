# Slang Flags

## Formal

Probably want to add a --formal flag, what is an example of a module that read_verilog handles differently with/without --formal

## Specify

what does the -specify flag on read_verilog do?

## Other

-noblackbox
-nomem2reg

# $initstate

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

# Interesting Tests

tests/abc_new/librelane
tests/abc_new/openroad
tests/arch
