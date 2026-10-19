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

tests/various/rand_const.ys
  - at least make it known that rand isn't supported anymore
tests/various/chparam.sh
  - IDK if this has an easy fix, I remember that slang has weird behavior with parameters but it should be documented at least
