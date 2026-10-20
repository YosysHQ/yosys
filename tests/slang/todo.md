# Slang Flags

-noblackbox
-nomem2reg
-specify
-formal

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
