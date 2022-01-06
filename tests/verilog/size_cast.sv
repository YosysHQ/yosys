module top;
    logic L1b0 = 0;
    logic L1b1 = 1;

    logic signed L1sb0 = 0;
    logic signed L1sb1 = 1;

    logic [1:0] L2b00 = 0;
    logic [1:0] L2b01 = 1;
    logic [1:0] L2b10 = 2;
    logic [1:0] L2b11 = 3;

    logic signed [1:0] L2sb00 = 0;
    logic signed [1:0] L2sb01 = 1;
    logic signed [1:0] L2sb10 = 2;
    logic signed [1:0] L2sb11 = 3;

    logic y = 1;

    always @* begin

        assert (1'(L1b0  ) == 1'b0);
        assert (1'(L1b1  ) == 1'b1);
        assert (1'(L1sb0 ) == 1'b0);
        assert (1'(L1sb1 ) == 1'b1);
        assert (1'(L2b00 ) == 1'b0);
        assert (1'(L2b01 ) == 1'b1);
        assert (1'(L2b10 ) == 1'b0);
        assert (1'(L2b11 ) == 1'b1);
        assert (1'(L2sb00) == 1'b0);
        assert (1'(L2sb01) == 1'b1);
        assert (1'(L2sb10) == 1'b0);
        assert (1'(L2sb11) == 1'b1);

        assert (2'(L1b0  ) == 2'b00);
        assert (2'(L1b1  ) == 2'b01);
        assert (2'(L1sb0 ) == 2'b00);
        assert (2'(L1sb1 ) == 2'b11);
        assert (2'(L2b00 ) == 2'b00);
        assert (2'(L2b01 ) == 2'b01);
        assert (2'(L2b10 ) == 2'b10);
        assert (2'(L2b11 ) == 2'b11);
        assert (2'(L2sb00) == 2'b00);
        assert (2'(L2sb01) == 2'b01);
        assert (2'(L2sb10) == 2'b10);
        assert (2'(L2sb11) == 2'b11);

        assert (3'(L1b0  ) == 3'b000);
        assert (3'(L1b1  ) == 3'b001);
        assert (3'(L1sb0 ) == 3'b000);
        assert (3'(L1sb1 ) == 3'b111);
        assert (3'(L2b00 ) == 3'b000);
        assert (3'(L2b01 ) == 3'b001);
        assert (3'(L2b10 ) == 3'b010);
        assert (3'(L2b11 ) == 3'b011);
        assert (3'(L2sb00) == 3'b000);
        assert (3'(L2sb01) == 3'b001);
        assert (3'(L2sb10) == 3'b110);
        assert (3'(L2sb11) == 3'b111);

        assert (3'(L1b0   | '1) == 3'b111);
        assert (3'(L1b1   | '1) == 3'b111);
        assert (3'(L1sb0  | '1) == 3'b111);
        assert (3'(L1sb1  | '1) == 3'b111);
        assert (3'(L2b00  | '1) == 3'b111);
        assert (3'(L2b01  | '1) == 3'b111);
        assert (3'(L2b10  | '1) == 3'b111);
        assert (3'(L2b11  | '1) == 3'b111);
        assert (3'(L2sb00 | '1) == 3'b111);
        assert (3'(L2sb01 | '1) == 3'b111);
        assert (3'(L2sb10 | '1) == 3'b111);
        assert (3'(L2sb11 | '1) == 3'b111);

        assert (3'(L1b0   | '0) == 3'b000);
        assert (3'(L1b1   | '0) == 3'b001);
        assert (3'(L1sb0  | '0) == 3'b000);
        assert (3'(L1sb1  | '0) == 3'b001);
        assert (3'(L2b00  | '0) == 3'b000);
        assert (3'(L2b01  | '0) == 3'b001);
        assert (3'(L2b10  | '0) == 3'b010);
        assert (3'(L2b11  | '0) == 3'b011);
        assert (3'(L2sb00 | '0) == 3'b000);
        assert (3'(L2sb01 | '0) == 3'b001);
        assert (3'(L2sb10 | '0) == 3'b010);
        assert (3'(L2sb11 | '0) == 3'b011);

        assert (3'(y ? L1b0   : '1) == 3'b000);
        assert (3'(y ? L1b1   : '1) == 3'b001);
        assert (3'(y ? L1sb0  : '1) == 3'b000);
        assert (3'(y ? L1sb1  : '1) == 3'b001);
        assert (3'(y ? L2b00  : '1) == 3'b000);
        assert (3'(y ? L2b01  : '1) == 3'b001);
        assert (3'(y ? L2b10  : '1) == 3'b010);
        assert (3'(y ? L2b11  : '1) == 3'b011);
        assert (3'(y ? L2sb00 : '1) == 3'b000);
        assert (3'(y ? L2sb01 : '1) == 3'b001);
        assert (3'(y ? L2sb10 : '1) == 3'b010);
        assert (3'(y ? L2sb11 : '1) == 3'b011);

        assert (3'(y ? L1b0   : '0) == 3'b000);
        assert (3'(y ? L1b1   : '0) == 3'b001);
        assert (3'(y ? L1sb0  : '0) == 3'b000);
        assert (3'(y ? L1sb1  : '0) == 3'b001);
        assert (3'(y ? L2b00  : '0) == 3'b000);
        assert (3'(y ? L2b01  : '0) == 3'b001);
        assert (3'(y ? L2b10  : '0) == 3'b010);
        assert (3'(y ? L2b11  : '0) == 3'b011);
        assert (3'(y ? L2sb00 : '0) == 3'b000);
        assert (3'(y ? L2sb01 : '0) == 3'b001);
        assert (3'(y ? L2sb10 : '0) == 3'b010);
        assert (3'(y ? L2sb11 : '0) == 3'b011);

        assert (3'(y ? L1b0   : 1'sb0) == 3'b000);
        assert (3'(y ? L1b1   : 1'sb0) == 3'b001);
        assert (3'(y ? L1sb0  : 1'sb0) == 3'b000);
        assert (3'(y ? L1sb1  : 1'sb0) == 3'b111);
        assert (3'(y ? L2b00  : 1'sb0) == 3'b000);
        assert (3'(y ? L2b01  : 1'sb0) == 3'b001);
        assert (3'(y ? L2b10  : 1'sb0) == 3'b010);
        assert (3'(y ? L2b11  : 1'sb0) == 3'b011);
        assert (3'(y ? L2sb00 : 1'sb0) == 3'b000);
        assert (3'(y ? L2sb01 : 1'sb0) == 3'b001);
        assert (3'(y ? L2sb10 : 1'sb0) == 3'b110);
        assert (3'(y ? L2sb11 : 1'sb0) == 3'b111);

        assert (3'(y ? L1b0   : 1'sb1) == 3'b000);
        assert (3'(y ? L1b1   : 1'sb1) == 3'b001);
        assert (3'(y ? L1sb0  : 1'sb1) == 3'b000);
        assert (3'(y ? L1sb1  : 1'sb1) == 3'b111);
        assert (3'(y ? L2b00  : 1'sb1) == 3'b000);
        assert (3'(y ? L2b01  : 1'sb1) == 3'b001);
        assert (3'(y ? L2b10  : 1'sb1) == 3'b010);
        assert (3'(y ? L2b11  : 1'sb1) == 3'b011);
        assert (3'(y ? L2sb00 : 1'sb1) == 3'b000);
        assert (3'(y ? L2sb01 : 1'sb1) == 3'b001);
        assert (3'(y ? L2sb10 : 1'sb1) == 3'b110);
        assert (3'(y ? L2sb11 : 1'sb1) == 3'b111);

    end
endmodule
