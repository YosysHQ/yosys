module \$lut (A, Y);
    parameter WIDTH = 0;
    parameter LUT = 0;

    input [WIDTH-1:0] A;
    output Y;

    function [WIDTH ** 2 - 1:0] INIT_address_inverse;
        input [WIDTH ** 2 - 1: 0] arr;
        integer i;
        integer n;
        reg [WIDTH - 1:0] tmp;
        reg [WIDTH - 1:0] tmp2;
        tmp = 0;
        tmp2 = 0;
        for (i = 0; i < WIDTH ** 2; i++) begin
            INIT_address_inverse[tmp2] = arr[tmp];
            tmp = tmp + 1;
            for (n = 0; n < WIDTH; n++) begin
                tmp2[WIDTH - 1 - n] = tmp[n];
            end
        end
    endfunction

    generate
        if (WIDTH == 1)
        begin
            LUT1 #(.INIT(INIT_address_inverse(LUT))) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]));
        end
        else if (WIDTH == 2)
        begin
            LUT2 #(.INIT(INIT_address_inverse(LUT))) _TECHMAP_REPLACE_ (.O(Y), .I0(A[1]), .I1(A[0]));
        end
        else if (WIDTH == 3)
        begin
            LUT3 #(.INIT(INIT_address_inverse(LUT))) _TECHMAP_REPLACE_ (.O(Y), .I0(A[2]), .I1(A[1]), .I2(A[0]));
        end
        else if (WIDTH == 4)
        begin
            LUT4 #(.INIT(INIT_address_inverse(LUT))) _TECHMAP_REPLACE_ (.O(Y), .I0(A[3]), .I1(A[2]), .I2(A[1]), .I3(A[0]));
        end
        else
        begin
            wire _TECHMAP_FAIL_ = 1;
        end
    endgenerate
endmodule
