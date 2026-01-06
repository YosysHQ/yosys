module MYMUL(A, B, Y);
    parameter WIDTH = 1;
    input [WIDTH-1:0] A, B;
    output reg [WIDTH-1:0] Y;

    wire [1023:0] _TECHMAP_DO_ = "proc; clean";

    integer i;
    always @* begin
        Y = 0;
        for (i = 0; i < WIDTH; i=i+1)
            if (A[i])
                Y = Y + (B << i);
    end
endmodule
