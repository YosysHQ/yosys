
## $initstate

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

## (any|all)|(seq|const)

```systemverilog
module top;
		(* anyseq *)
    wire a;
    (* anyconst *)
    wire b;
    (* allseq *)
    wire c;
    (* allseq *)
    wire d;
    
endmodule
```

assert count one of each type
