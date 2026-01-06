module \$reduce_or (A, Y);

    parameter A_SIGNED = 0;
    parameter A_WIDTH = 0;
    parameter Y_WIDTH = 0;

    input [A_WIDTH-1:0] A;
    output [Y_WIDTH-1:0] Y;

    function integer min;
        input integer a, b;
        begin
            if (a < b)
                min = a;
            else
                min = b;
        end
    endfunction

    genvar i;
    generate begin
        if (A_WIDTH == 0) begin
            assign Y = 0;
        end
        if (A_WIDTH == 1) begin
            assign Y = A;
        end
        if (A_WIDTH == 2) begin
            wire ybuf;
            OR3X1 g (.A(A[0]), .B(A[1]), .C(1'b0), .Y(ybuf));
            assign Y = ybuf;
        end
        if (A_WIDTH == 3) begin
            wire ybuf;
            OR3X1 g (.A(A[0]), .B(A[1]), .C(A[2]), .Y(ybuf));
            assign Y = ybuf;
        end
        if (A_WIDTH > 3) begin
            localparam next_stage_sz = (A_WIDTH+2) / 3;
            wire [next_stage_sz-1:0] next_stage;
            for (i = 0; i < next_stage_sz; i = i+1) begin
                localparam bits = min(A_WIDTH - 3*i, 3);
                assign next_stage[i] = |A[3*i +: bits];
            end
            assign Y = |next_stage;
        end
    end endgenerate
endmodule
