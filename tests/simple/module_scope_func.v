// Some strict implementatins either forbid hierarchical identifiers within
// constant expressions, or forbid declaring functions in generate blocks, or
// both. Yosys and Iverilog are not strict in either of these ways.
module module_scope_func_top(
    input wire inp,
    output wire [31:0] out1, out2, out4, out5, out7, out8,
    output reg [31:0] out3, out6, out9
);
    function automatic integer incr;
        input integer value;
        incr = value + 1;
    endfunction
    task send;
        output integer out;
        out = 55;
    endtask

    assign out1 = module_scope_func_top.incr(inp);
    localparam C = module_scope_func_top.incr(10);
    assign out2 = C;
    initial module_scope_func_top.send(out3);

    if (1) begin : blk
        // shadows module_scope_func_top.incr
        function automatic integer incr;
            input integer value;
            incr = value * 2;
        endfunction
        // shadows module_scope_func_top.send
        task send;
            output integer out;
            out = 66;
        endtask

        assign out4 = module_scope_func_top.incr(inp);
        localparam D = module_scope_func_top.incr(20);
        assign out5 = D;
        initial module_scope_func_top.send(out6);

        assign out7 = incr(inp);
        localparam E = incr(30);
        assign out8 = E;
        initial send(out9);
    end
endmodule
