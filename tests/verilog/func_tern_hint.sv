module top;
    function automatic [30:0] func;
        input integer inp;
        func = { // self-determined context
            (
                inp == 0
                ? -1 // causes whole ternary to be 32 bits
                : func(inp - 1) // 31 bits, unsigned
            ) >> 2};
    endfunction
    function automatic signed [3:0] dunk;
        input integer inp;
        dunk = (
                inp == 0
                ? 4'hF
                // shouldn't make the ternary signed
                : dunk(inp - 1)
            ) == -1;
    endfunction
    localparam A = func(0);
    localparam B = func(1);
    localparam C = func(2);
    localparam D = func(3);
    localparam X = dunk(0);
    localparam Y = dunk(1);
    initial begin
        assert(A == 31'h3F_FFFFFF);
        assert(B == 31'h0F_FFFFFF);
        assert(C == 31'h03_FFFFFF);
        assert(D == 31'h00_FFFFFF);
        assert(X == 0);
        assert(Y == 0);
    end
    initial begin
        logic x;
        case (1'b1)
            dunk(0): x = 0;
            default: x = 1;
        endcase
        assert(x);
    end
endmodule
