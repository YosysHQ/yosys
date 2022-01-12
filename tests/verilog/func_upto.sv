`default_nettype none

module evil;
    parameter HI = 3;
    parameter LO = 0;
    parameter SPAN = 1;
    parameter [HI:LO] A_VAL = 4'b0110;
    parameter [HI:LO] B_VAL = 4'b1100;
    parameter [2:0] SWAPS = 0;

    localparam D_LEFT  = !(SWAPS[0]) ? HI : LO;
    localparam D_RIGHT =  (SWAPS[0]) ? HI : LO;
    localparam E_LEFT  = !(SWAPS[1]) ? HI : LO;
    localparam E_RIGHT =  (SWAPS[1]) ? HI : LO;
    localparam F_LEFT  = !(SWAPS[2]) ? HI : LO;
    localparam F_RIGHT =  (SWAPS[2]) ? HI : LO;

    localparam [HI:LO] A_CONST = A_VAL;
    localparam [HI:LO] B_CONST = B_VAL;
    localparam [HI:LO] C_CONST = F(A_CONST, B_CONST);

    reg [HI:LO] C_WIRE, C_FUNC;
    always @* begin
        assert (C_CONST == C_WIRE);
        assert (C_CONST == C_FUNC);
    end

    initial begin : blk
        reg [HI:LO] A_WIRE;
        reg [HI:LO] B_WIRE;
        reg [D_LEFT:D_RIGHT] D;
        reg [E_LEFT:E_RIGHT] E;
        reg [F_LEFT:F_RIGHT] F_WIRE;
        reg [31:0] i;
        A_WIRE = A_VAL;
        B_WIRE = B_VAL;
        D = A_WIRE;
        E = B_WIRE;
        F_WIRE = 0;
        for (i = LO; i + SPAN < HI; i = i + SPAN)
            if (SPAN == 1)
                F_WIRE[i] = D[i] && E[i];
            else
                F_WIRE[i+:SPAN] = D[i+:SPAN] && E[i+:SPAN];
        C_WIRE = F_WIRE;
        C_FUNC = F(A_WIRE, B_WIRE);
    end

    function automatic [F_LEFT:F_RIGHT] F(
        input [D_LEFT:D_RIGHT] D,
        input [E_LEFT:E_RIGHT] E);
        reg [31:0] i;
        F = 0;
        for (i = LO; i + SPAN < HI; i = i + SPAN)
            if (SPAN == 1)
                F[i] = D[i] && E[i];
            else
                F[i+:SPAN] = D[i+:SPAN] && E[i+:SPAN];
    endfunction
endmodule

module top;
    for (genvar hi = 0; hi < 3; hi++)
    for (genvar lo = 0; lo <= hi; lo++)
    for (genvar span = 1; span <= hi - lo + 1; span++)
    for (genvar a_val = 0; a_val < 2 ** (hi - lo + 1); a_val++)
    for (genvar b_val = 0; b_val < 2 ** (hi - lo + 1); b_val++)
    for (genvar swaps = 0; swaps < 2 ** 3; swaps++)
        evil #(
            .HI(hi),
            .LO(lo),
            .SPAN(span),
            .A_VAL(a_val),
            .B_VAL(b_val),
            .SWAPS(swaps)
        ) e();
endmodule
