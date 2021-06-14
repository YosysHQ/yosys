module top(
    output reg [7:0]
    out1, out2, out3, out4
);
    initial begin
        begin : blk1
            reg x;
            x = 1;
        end
        out1 = blk1.x;
        begin : blk2
            reg x;
            x = 2;
        end : blk2
        out2 = blk2.x;
    end
    if (1) begin
        if (1) begin : blk3
            reg x;
            assign x = 3;
        end
        assign out3 = blk3.x;
        if (1) begin : blk4
            reg x;
            assign x = 4;
        end : blk4
        assign out4 = blk4.x;
    end
endmodule
