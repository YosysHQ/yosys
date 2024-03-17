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

    typedef logic              u1bit_t;
    typedef logic signed       s1bit_t;
    typedef logic        [1:0] u2bit_t;
    typedef logic signed [1:0] s2bit_t;
    typedef logic        [2:0] u3bit_t; 

    typedef struct packed {
	    u1bit_t sign;
	    u3bit_t msbs;
	    byte    lsbs;
    } s12bit_packed_struct_t;


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

        assert (u1bit_t'(L1b0  ) == 1'b0);
        assert (u1bit_t'(L1b1  ) == 1'b1);
        assert (s1bit_t'(L1sb0 ) == 1'b0);
        assert (s1bit_t'(L1sb1 ) == 1'b1);
        assert (u1bit_t'(L2b00 ) == 1'b0);
        assert (u1bit_t'(L2b01 ) == 1'b1);
        assert (u1bit_t'(L2b10 ) == 1'b0);
        assert (u1bit_t'(L2b11 ) == 1'b1);
        assert (s1bit_t'(L2sb00) == 1'b0);
        assert (s1bit_t'(L2sb01) == 1'b1);
        assert (s1bit_t'(L2sb10) == 1'b0);
        assert (s1bit_t'(L2sb11) == 1'b1);


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

        assert (u2bit_t'(L1b0  ) == 2'b00);
        assert (u2bit_t'(L1b1  ) == 2'b01);
        assert (s2bit_t'(L1sb0 ) == 2'b00);
        assert (s2bit_t'(L1sb1 ) == 2'b11);
        assert (u2bit_t'(L2b00 ) == 2'b00);
        assert (u2bit_t'(L2b01 ) == 2'b01);
        assert (u2bit_t'(L2b10 ) == 2'b10);
        assert (u2bit_t'(L2b11 ) == 2'b11);
        assert (s2bit_t'(L2sb00) == 2'b00);
        assert (s2bit_t'(L2sb01) == 2'b01);
        assert (s2bit_t'(L2sb10) == 2'b10);
        assert (s2bit_t'(L2sb11) == 2'b11);


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

        assert (u3bit_t'(L1b0  ) == 3'b000);
        assert (u3bit_t'(L1b1  ) == 3'b001);
        assert (u3bit_t'(L1sb0 ) == 3'b000);
        assert (u3bit_t'(L1sb1 ) == 3'b111);
        assert (u3bit_t'(L2b00 ) == 3'b000);
        assert (u3bit_t'(L2b01 ) == 3'b001);
        assert (u3bit_t'(L2b10 ) == 3'b010);
        assert (u3bit_t'(L2b11 ) == 3'b011);
        assert (u3bit_t'(L2sb00) == 3'b000);
        assert (u3bit_t'(L2sb01) == 3'b001);
        assert (u3bit_t'(L2sb10) == 3'b110);
        assert (u3bit_t'(L2sb11) == 3'b111);


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

        assert (u3bit_t'(L1b0   | '1) == 3'b111);
        assert (u3bit_t'(L1b1   | '1) == 3'b111);
        assert (u3bit_t'(L1sb0  | '1) == 3'b111);
        assert (u3bit_t'(L1sb1  | '1) == 3'b111);
        assert (u3bit_t'(L2b00  | '1) == 3'b111);
        assert (u3bit_t'(L2b01  | '1) == 3'b111);
        assert (u3bit_t'(L2b10  | '1) == 3'b111);
        assert (u3bit_t'(L2b11  | '1) == 3'b111);
        assert (u3bit_t'(L2sb00 | '1) == 3'b111);
        assert (u3bit_t'(L2sb01 | '1) == 3'b111);
        assert (u3bit_t'(L2sb10 | '1) == 3'b111);
        assert (u3bit_t'(L2sb11 | '1) == 3'b111);

        assert (byte'(L1b0   | '1) == 8'hff);
        assert (byte'(L1b1   | '1) == 8'hff);
        assert (byte'(L1sb0  | '1) == 8'hff);
        assert (byte'(L1sb1  | '1) == 8'hff);
        assert (byte'(L2b00  | '1) == 8'hff);
        assert (byte'(L2b01  | '1) == 8'hff);
        assert (byte'(L2b10  | '1) == 8'hff);
        assert (byte'(L2b11  | '1) == 8'hff);
        assert (byte'(L2sb00 | '1) == 8'hff);
        assert (byte'(L2sb01 | '1) == 8'hff);
        assert (byte'(L2sb10 | '1) == 8'hff);
        assert (byte'(L2sb11 | '1) == 8'hff);

        assert (int'(L1b0   | '1) == 32'hffff_ffff);
        assert (int'(L1b1   | '1) == 32'hffff_ffff);
        assert (int'(L1sb0  | '1) == 32'hffff_ffff);
        assert (int'(L1sb1  | '1) == 32'hffff_ffff);
        assert (int'(L2b00  | '1) == 32'hffff_ffff);
        assert (int'(L2b01  | '1) == 32'hffff_ffff);
        assert (int'(L2b10  | '1) == 32'hffff_ffff);
        assert (int'(L2b11  | '1) == 32'hffff_ffff);
        assert (int'(L2sb00 | '1) == 32'hffff_ffff);
        assert (int'(L2sb01 | '1) == 32'hffff_ffff);
        assert (int'(L2sb10 | '1) == 32'hffff_ffff);
        assert (int'(L2sb11 | '1) == 32'hffff_ffff);

        assert (s12bit_packed_struct_t'(L1b0   | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L1b1   | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L1sb0  | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L1sb1  | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L2b00  | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L2b01  | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L2b10  | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L2b11  | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L2sb00 | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L2sb01 | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L2sb10 | '1) == 12'hfff);
        assert (s12bit_packed_struct_t'(L2sb11 | '1) == 12'hfff);


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

        assert (u3bit_t'(L1b0   | '0) == 3'b000);
        assert (u3bit_t'(L1b1   | '0) == 3'b001);
        assert (u3bit_t'(L1sb0  | '0) == 3'b000);
        assert (u3bit_t'(L1sb1  | '0) == 3'b001);
        assert (u3bit_t'(L2b00  | '0) == 3'b000);
        assert (u3bit_t'(L2b01  | '0) == 3'b001);
        assert (u3bit_t'(L2b10  | '0) == 3'b010);
        assert (u3bit_t'(L2b11  | '0) == 3'b011);
        assert (u3bit_t'(L2sb00 | '0) == 3'b000);
        assert (u3bit_t'(L2sb01 | '0) == 3'b001);
        assert (u3bit_t'(L2sb10 | '0) == 3'b010);
        assert (u3bit_t'(L2sb11 | '0) == 3'b011);

	assert (byte'(L1b0   | '0) == 8'h00);
        assert (byte'(L1b1   | '0) == 8'h01);
        assert (byte'(L1sb0  | '0) == 8'h00);
        assert (byte'(L1sb1  | '0) == 8'h01);
        assert (byte'(L2b00  | '0) == 8'h00);
        assert (byte'(L2b01  | '0) == 8'h01);
        assert (byte'(L2b10  | '0) == 8'h02);
        assert (byte'(L2b11  | '0) == 8'h03);
        assert (byte'(L2sb00 | '0) == 8'h00);
        assert (byte'(L2sb01 | '0) == 8'h01);
        assert (byte'(L2sb10 | '0) == 8'h02);
        assert (byte'(L2sb11 | '0) == 8'h03);

        assert (int'(L1b0   | '0) == 32'h0000_0000);
        assert (int'(L1b1   | '0) == 32'h0000_0001);
        assert (int'(L1sb0  | '0) == 32'h0000_0000);
        assert (int'(L1sb1  | '0) == 32'h0000_0001);
        assert (int'(L2b00  | '0) == 32'h0000_0000);
        assert (int'(L2b01  | '0) == 32'h0000_0001);
        assert (int'(L2b10  | '0) == 32'h0000_0002);
        assert (int'(L2b11  | '0) == 32'h0000_0003);
        assert (int'(L2sb00 | '0) == 32'h0000_0000);
        assert (int'(L2sb01 | '0) == 32'h0000_0001);
        assert (int'(L2sb10 | '0) == 32'h0000_0002);
        assert (int'(L2sb11 | '0) == 32'h0000_0003);

        assert (s12bit_packed_struct_t'(L1b0   | '0) == 12'h000);
        assert (s12bit_packed_struct_t'(L1b1   | '0) == 12'h001);
        assert (s12bit_packed_struct_t'(L1sb0  | '0) == 12'h000);
        assert (s12bit_packed_struct_t'(L1sb1  | '0) == 12'h001);
        assert (s12bit_packed_struct_t'(L2b00  | '0) == 12'h000);
        assert (s12bit_packed_struct_t'(L2b01  | '0) == 12'h001);
        assert (s12bit_packed_struct_t'(L2b10  | '0) == 12'h002);
        assert (s12bit_packed_struct_t'(L2b11  | '0) == 12'h003);
        assert (s12bit_packed_struct_t'(L2sb00 | '0) == 12'h000);
        assert (s12bit_packed_struct_t'(L2sb01 | '0) == 12'h001);
        assert (s12bit_packed_struct_t'(L2sb10 | '0) == 12'h002);
        assert (s12bit_packed_struct_t'(L2sb11 | '0) == 12'h003);


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

        assert (u3bit_t'(y ? L1b0   : '1) == 3'b000);
        assert (u3bit_t'(y ? L1b1   : '1) == 3'b001);
        assert (u3bit_t'(y ? L1sb0  : '1) == 3'b000);
        assert (u3bit_t'(y ? L1sb1  : '1) == 3'b001);
        assert (u3bit_t'(y ? L2b00  : '1) == 3'b000);
        assert (u3bit_t'(y ? L2b01  : '1) == 3'b001);
        assert (u3bit_t'(y ? L2b10  : '1) == 3'b010);
        assert (u3bit_t'(y ? L2b11  : '1) == 3'b011);
        assert (u3bit_t'(y ? L2sb00 : '1) == 3'b000);
        assert (u3bit_t'(y ? L2sb01 : '1) == 3'b001);
        assert (u3bit_t'(y ? L2sb10 : '1) == 3'b010);
        assert (u3bit_t'(y ? L2sb11 : '1) == 3'b011);

	assert (byte'(y ? L1b0   : '1) == 8'h00);
        assert (byte'(y ? L1b1   : '1) == 8'h01);
        assert (byte'(y ? L1sb0  : '1) == 8'h00);
        assert (byte'(y ? L1sb1  : '1) == 8'h01);
        assert (byte'(y ? L2b00  : '1) == 8'h00);
        assert (byte'(y ? L2b01  : '1) == 8'h01);
        assert (byte'(y ? L2b10  : '1) == 8'h02);
        assert (byte'(y ? L2b11  : '1) == 8'h03);
        assert (byte'(y ? L2sb00 : '1) == 8'h00);
        assert (byte'(y ? L2sb01 : '1) == 8'h01);
        assert (byte'(y ? L2sb10 : '1) == 8'h02);
        assert (byte'(y ? L2sb11 : '1) == 8'h03);

        assert (int'(y ? L1b0   : '1) == 32'h0000_0000);
        assert (int'(y ? L1b1   : '1) == 32'h0000_0001);
        assert (int'(y ? L1sb0  : '1) == 32'h0000_0000);
        assert (int'(y ? L1sb1  : '1) == 32'h0000_0001);
        assert (int'(y ? L2b00  : '1) == 32'h0000_0000);
        assert (int'(y ? L2b01  : '1) == 32'h0000_0001);
        assert (int'(y ? L2b10  : '1) == 32'h0000_0002);
        assert (int'(y ? L2b11  : '1) == 32'h0000_0003);
        assert (int'(y ? L2sb00 : '1) == 32'h0000_0000);
        assert (int'(y ? L2sb01 : '1) == 32'h0000_0001);
        assert (int'(y ? L2sb10 : '1) == 32'h0000_0002);
        assert (int'(y ? L2sb11 : '1) == 32'h0000_0003);

        assert (s12bit_packed_struct_t'(y ? L1b0   : '1) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1b1   : '1) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L1sb0  : '1) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1sb1  : '1) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2b00  : '1) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2b01  : '1) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2b10  : '1) == 12'h002);
        assert (s12bit_packed_struct_t'(y ? L2b11  : '1) == 12'h003);
        assert (s12bit_packed_struct_t'(y ? L2sb00 : '1) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2sb01 : '1) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2sb10 : '1) == 12'h002);
        assert (s12bit_packed_struct_t'(y ? L2sb11 : '1) == 12'h003);


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

        assert (u3bit_t'(y ? L1b0   : '0) == 3'b000);
        assert (u3bit_t'(y ? L1b1   : '0) == 3'b001);
        assert (u3bit_t'(y ? L1sb0  : '0) == 3'b000);
        assert (u3bit_t'(y ? L1sb1  : '0) == 3'b001);
        assert (u3bit_t'(y ? L2b00  : '0) == 3'b000);
        assert (u3bit_t'(y ? L2b01  : '0) == 3'b001);
        assert (u3bit_t'(y ? L2b10  : '0) == 3'b010);
        assert (u3bit_t'(y ? L2b11  : '0) == 3'b011);
        assert (u3bit_t'(y ? L2sb00 : '0) == 3'b000);
        assert (u3bit_t'(y ? L2sb01 : '0) == 3'b001);
        assert (u3bit_t'(y ? L2sb10 : '0) == 3'b010);
        assert (u3bit_t'(y ? L2sb11 : '0) == 3'b011);

	assert (byte'(y ? L1b0   : '0) == 8'h00);
        assert (byte'(y ? L1b1   : '0) == 8'h01);
        assert (byte'(y ? L1sb0  : '0) == 8'h00);
        assert (byte'(y ? L1sb1  : '0) == 8'h01);
        assert (byte'(y ? L2b00  : '0) == 8'h00);
        assert (byte'(y ? L2b01  : '0) == 8'h01);
        assert (byte'(y ? L2b10  : '0) == 8'h02);
        assert (byte'(y ? L2b11  : '0) == 8'h03);
        assert (byte'(y ? L2sb00 : '0) == 8'h00);
        assert (byte'(y ? L2sb01 : '0) == 8'h01);
        assert (byte'(y ? L2sb10 : '0) == 8'h02);
        assert (byte'(y ? L2sb11 : '0) == 8'h03);
	
        assert (int'(y ? L1b0   : '0) == 32'h0000_0000);
        assert (int'(y ? L1b1   : '0) == 32'h0000_0001);
        assert (int'(y ? L1sb0  : '0) == 32'h0000_0000);
        assert (int'(y ? L1sb1  : '0) == 32'h0000_0001);
        assert (int'(y ? L2b00  : '0) == 32'h0000_0000);
        assert (int'(y ? L2b01  : '0) == 32'h0000_0001);
        assert (int'(y ? L2b10  : '0) == 32'h0000_0002);
        assert (int'(y ? L2b11  : '0) == 32'h0000_0003);
        assert (int'(y ? L2sb00 : '0) == 32'h0000_0000);
        assert (int'(y ? L2sb01 : '0) == 32'h0000_0001);
        assert (int'(y ? L2sb10 : '0) == 32'h0000_0002);
        assert (int'(y ? L2sb11 : '0) == 32'h0000_0003);

        assert (s12bit_packed_struct_t'(y ? L1b0   : '0) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1b1   : '0) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L1sb0  : '0) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1sb1  : '0) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2b00  : '0) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2b01  : '0) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2b10  : '0) == 12'h002);
        assert (s12bit_packed_struct_t'(y ? L2b11  : '0) == 12'h003);
        assert (s12bit_packed_struct_t'(y ? L2sb00 : '0) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2sb01 : '0) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2sb10 : '0) == 12'h002);
        assert (s12bit_packed_struct_t'(y ? L2sb11 : '0) == 12'h003);
	

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

        assert (u3bit_t'(y ? L1b0   : 1'sb0) == 3'b000);
        assert (u3bit_t'(y ? L1b1   : 1'sb0) == 3'b001);
        assert (u3bit_t'(y ? L1sb0  : 1'sb0) == 3'b000);
        assert (u3bit_t'(y ? L1sb1  : 1'sb0) == 3'b111);
        assert (u3bit_t'(y ? L2b00  : 1'sb0) == 3'b000);
        assert (u3bit_t'(y ? L2b01  : 1'sb0) == 3'b001);
        assert (u3bit_t'(y ? L2b10  : 1'sb0) == 3'b010);
        assert (u3bit_t'(y ? L2b11  : 1'sb0) == 3'b011);
        assert (u3bit_t'(y ? L2sb00 : 1'sb0) == 3'b000);
        assert (u3bit_t'(y ? L2sb01 : 1'sb0) == 3'b001);
        assert (u3bit_t'(y ? L2sb10 : 1'sb0) == 3'b110);
        assert (u3bit_t'(y ? L2sb11 : 1'sb0) == 3'b111);

	assert (byte'(y ? L1b0   : 1'sb0) == 8'h00);
        assert (byte'(y ? L1b1   : 1'sb0) == 8'h01);
        assert (byte'(y ? L1sb0  : 1'sb0) == 8'h00);
        assert (byte'(y ? L1sb1  : 1'sb0) == 8'hff);
        assert (byte'(y ? L2b00  : 1'sb0) == 8'h00);
        assert (byte'(y ? L2b01  : 1'sb0) == 8'h01);
        assert (byte'(y ? L2b10  : 1'sb0) == 8'h02);
        assert (byte'(y ? L2b11  : 1'sb0) == 8'h03);
        assert (byte'(y ? L2sb00 : 1'sb0) == 8'h00);
        assert (byte'(y ? L2sb01 : 1'sb0) == 8'h01);
        assert (byte'(y ? L2sb10 : 1'sb0) == 8'hfe);
        assert (byte'(y ? L2sb11 : 1'sb0) == 8'hff);

        assert (int'(y ? L1b0   : 1'sb0) == 32'h0000_0000);
        assert (int'(y ? L1b1   : 1'sb0) == 32'h0000_0001);
        assert (int'(y ? L1sb0  : 1'sb0) == 32'h0000_0000);
        assert (int'(y ? L1sb1  : 1'sb0) == 32'hffff_ffff);
        assert (int'(y ? L2b00  : 1'sb0) == 32'h0000_0000);
        assert (int'(y ? L2b01  : 1'sb0) == 32'h0000_0001);
        assert (int'(y ? L2b10  : 1'sb0) == 32'h0000_0002);
        assert (int'(y ? L2b11  : 1'sb0) == 32'h0000_0003);
        assert (int'(y ? L2sb00 : 1'sb0) == 32'h0000_0000);
        assert (int'(y ? L2sb01 : 1'sb0) == 32'h0000_0001);
        assert (int'(y ? L2sb10 : 1'sb0) == 32'hffff_fffe);
        assert (int'(y ? L2sb11 : 1'sb0) == 32'hffff_ffff);

        assert (s12bit_packed_struct_t'(y ? L1b0   : 1'sb0) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1b1   : 1'sb0) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L1sb0  : 1'sb0) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1sb1  : 1'sb0) == 12'hfff);
        assert (s12bit_packed_struct_t'(y ? L2b00  : 1'sb0) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2b01  : 1'sb0) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2b10  : 1'sb0) == 12'h002);
        assert (s12bit_packed_struct_t'(y ? L2b11  : 1'sb0) == 12'h003);
        assert (s12bit_packed_struct_t'(y ? L2sb00 : 1'sb0) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2sb01 : 1'sb0) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2sb10 : 1'sb0) == 12'hffe);
        assert (s12bit_packed_struct_t'(y ? L2sb11 : 1'sb0) == 12'hfff);

        assert (3'(y ? L1b0   : s1bit_t'(0)) == 3'b000);
        assert (3'(y ? L1b1   : s1bit_t'(0)) == 3'b001);
        assert (3'(y ? L1sb0  : s1bit_t'(0)) == 3'b000);
        assert (3'(y ? L1sb1  : s1bit_t'(0)) == 3'b111);
        assert (3'(y ? L2b00  : s1bit_t'(0)) == 3'b000);
        assert (3'(y ? L2b01  : s1bit_t'(0)) == 3'b001);
        assert (3'(y ? L2b10  : s1bit_t'(0)) == 3'b010);
        assert (3'(y ? L2b11  : s1bit_t'(0)) == 3'b011);
        assert (3'(y ? L2sb00 : s1bit_t'(0)) == 3'b000);
        assert (3'(y ? L2sb01 : s1bit_t'(0)) == 3'b001);
        assert (3'(y ? L2sb10 : s1bit_t'(0)) == 3'b110);
        assert (3'(y ? L2sb11 : s1bit_t'(0)) == 3'b111);

        assert (u3bit_t'(y ? L1b0   : s1bit_t'(0)) == 3'b000);
        assert (u3bit_t'(y ? L1b1   : s1bit_t'(0)) == 3'b001);
        assert (u3bit_t'(y ? L1sb0  : s1bit_t'(0)) == 3'b000);
        assert (u3bit_t'(y ? L1sb1  : s1bit_t'(0)) == 3'b111);
        assert (u3bit_t'(y ? L2b00  : s1bit_t'(0)) == 3'b000);
        assert (u3bit_t'(y ? L2b01  : s1bit_t'(0)) == 3'b001);
        assert (u3bit_t'(y ? L2b10  : s1bit_t'(0)) == 3'b010);
        assert (u3bit_t'(y ? L2b11  : s1bit_t'(0)) == 3'b011);
        assert (u3bit_t'(y ? L2sb00 : s1bit_t'(0)) == 3'b000);
        assert (u3bit_t'(y ? L2sb01 : s1bit_t'(0)) == 3'b001);
        assert (u3bit_t'(y ? L2sb10 : s1bit_t'(0)) == 3'b110);
        assert (u3bit_t'(y ? L2sb11 : s1bit_t'(0)) == 3'b111);

	assert (byte'(y ? L1b0   : s1bit_t'(0)) == 8'h00);
        assert (byte'(y ? L1b1   : s1bit_t'(0)) == 8'h01);
        assert (byte'(y ? L1sb0  : s1bit_t'(0)) == 8'h00);
        assert (byte'(y ? L1sb1  : s1bit_t'(0)) == 8'hff);
        assert (byte'(y ? L2b00  : s1bit_t'(0)) == 8'h00);
        assert (byte'(y ? L2b01  : s1bit_t'(0)) == 8'h01);
        assert (byte'(y ? L2b10  : s1bit_t'(0)) == 8'h02);
        assert (byte'(y ? L2b11  : s1bit_t'(0)) == 8'h03);
        assert (byte'(y ? L2sb00 : s1bit_t'(0)) == 8'h00);
        assert (byte'(y ? L2sb01 : s1bit_t'(0)) == 8'h01);
        assert (byte'(y ? L2sb10 : s1bit_t'(0)) == 8'hfe);
        assert (byte'(y ? L2sb11 : s1bit_t'(0)) == 8'hff);

        assert (int'(y ? L1b0   : s1bit_t'(0)) == 32'h0000_0000);
        assert (int'(y ? L1b1   : s1bit_t'(0)) == 32'h0000_0001);
        assert (int'(y ? L1sb0  : s1bit_t'(0)) == 32'h0000_0000);
        assert (int'(y ? L1sb1  : s1bit_t'(0)) == 32'hffff_ffff);
        assert (int'(y ? L2b00  : s1bit_t'(0)) == 32'h0000_0000);
        assert (int'(y ? L2b01  : s1bit_t'(0)) == 32'h0000_0001);
        assert (int'(y ? L2b10  : s1bit_t'(0)) == 32'h0000_0002);
        assert (int'(y ? L2b11  : s1bit_t'(0)) == 32'h0000_0003);
        assert (int'(y ? L2sb00 : s1bit_t'(0)) == 32'h0000_0000);
        assert (int'(y ? L2sb01 : s1bit_t'(0)) == 32'h0000_0001);
        assert (int'(y ? L2sb10 : s1bit_t'(0)) == 32'hffff_fffe);
        assert (int'(y ? L2sb11 : s1bit_t'(0)) == 32'hffff_ffff);

        assert (s12bit_packed_struct_t'(y ? L1b0   : s1bit_t'(0)) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1b1   : s1bit_t'(0)) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L1sb0  : s1bit_t'(0)) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1sb1  : s1bit_t'(0)) == 12'hfff);
        assert (s12bit_packed_struct_t'(y ? L2b00  : s1bit_t'(0)) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2b01  : s1bit_t'(0)) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2b10  : s1bit_t'(0)) == 12'h002);
        assert (s12bit_packed_struct_t'(y ? L2b11  : s1bit_t'(0)) == 12'h003);
        assert (s12bit_packed_struct_t'(y ? L2sb00 : s1bit_t'(0)) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2sb01 : s1bit_t'(0)) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2sb10 : s1bit_t'(0)) == 12'hffe);
        assert (s12bit_packed_struct_t'(y ? L2sb11 : s1bit_t'(0)) == 12'hfff);


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

        assert (u3bit_t'(y ? L1b0   : 1'sb1) == 3'b000);
        assert (u3bit_t'(y ? L1b1   : 1'sb1) == 3'b001);
        assert (u3bit_t'(y ? L1sb0  : 1'sb1) == 3'b000);
        assert (u3bit_t'(y ? L1sb1  : 1'sb1) == 3'b111);
        assert (u3bit_t'(y ? L2b00  : 1'sb1) == 3'b000);
        assert (u3bit_t'(y ? L2b01  : 1'sb1) == 3'b001);
        assert (u3bit_t'(y ? L2b10  : 1'sb1) == 3'b010);
        assert (u3bit_t'(y ? L2b11  : 1'sb1) == 3'b011);
        assert (u3bit_t'(y ? L2sb00 : 1'sb1) == 3'b000);
        assert (u3bit_t'(y ? L2sb01 : 1'sb1) == 3'b001);
        assert (u3bit_t'(y ? L2sb10 : 1'sb1) == 3'b110);
        assert (u3bit_t'(y ? L2sb11 : 1'sb1) == 3'b111);

	assert (byte'(y ? L1b0   : 1'sb1) == 8'h00);
        assert (byte'(y ? L1b1   : 1'sb1) == 8'h01);
        assert (byte'(y ? L1sb0  : 1'sb1) == 8'h00);
        assert (byte'(y ? L1sb1  : 1'sb1) == 8'hff);
        assert (byte'(y ? L2b00  : 1'sb1) == 8'h00);
        assert (byte'(y ? L2b01  : 1'sb1) == 8'h01);
        assert (byte'(y ? L2b10  : 1'sb1) == 8'h02);
        assert (byte'(y ? L2b11  : 1'sb1) == 8'h03);
        assert (byte'(y ? L2sb00 : 1'sb1) == 8'h00);
        assert (byte'(y ? L2sb01 : 1'sb1) == 8'h01);
        assert (byte'(y ? L2sb10 : 1'sb1) == 8'hfe);
        assert (byte'(y ? L2sb11 : 1'sb1) == 8'hff);

        assert (int'(y ? L1b0   : 1'sb1) == 32'h0000_0000);
        assert (int'(y ? L1b1   : 1'sb1) == 32'h0000_0001);
        assert (int'(y ? L1sb0  : 1'sb1) == 32'h0000_0000);
        assert (int'(y ? L1sb1  : 1'sb1) == 32'hffff_ffff);
        assert (int'(y ? L2b00  : 1'sb1) == 32'h0000_0000);
        assert (int'(y ? L2b01  : 1'sb1) == 32'h0000_0001);
        assert (int'(y ? L2b10  : 1'sb1) == 32'h0000_0002);
        assert (int'(y ? L2b11  : 1'sb1) == 32'h0000_0003);
        assert (int'(y ? L2sb00 : 1'sb1) == 32'h0000_0000);
        assert (int'(y ? L2sb01 : 1'sb1) == 32'h0000_0001);
        assert (int'(y ? L2sb10 : 1'sb1) == 32'hffff_fffe);
        assert (int'(y ? L2sb11 : 1'sb1) == 32'hffff_ffff);

        assert (s12bit_packed_struct_t'(y ? L1b0   : 1'sb1) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1b1   : 1'sb1) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L1sb0  : 1'sb1) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1sb1  : 1'sb1) == 12'hfff);
        assert (s12bit_packed_struct_t'(y ? L2b00  : 1'sb1) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2b01  : 1'sb1) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2b10  : 1'sb1) == 12'h002);
        assert (s12bit_packed_struct_t'(y ? L2b11  : 1'sb1) == 12'h003);
        assert (s12bit_packed_struct_t'(y ? L2sb00 : 1'sb1) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2sb01 : 1'sb1) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2sb10 : 1'sb1) == 12'hffe);
        assert (s12bit_packed_struct_t'(y ? L2sb11 : 1'sb1) == 12'hfff);

        assert (3'(y ? L1b0   : s1bit_t'(1)) == 3'b000);
        assert (3'(y ? L1b1   : s1bit_t'(1)) == 3'b001);
        assert (3'(y ? L1sb0  : s1bit_t'(1)) == 3'b000);
        assert (3'(y ? L1sb1  : s1bit_t'(1)) == 3'b111);
        assert (3'(y ? L2b00  : s1bit_t'(1)) == 3'b000);
        assert (3'(y ? L2b01  : s1bit_t'(1)) == 3'b001);
        assert (3'(y ? L2b10  : s1bit_t'(1)) == 3'b010);
        assert (3'(y ? L2b11  : s1bit_t'(1)) == 3'b011);
        assert (3'(y ? L2sb00 : s1bit_t'(1)) == 3'b000);
        assert (3'(y ? L2sb01 : s1bit_t'(1)) == 3'b001);
        assert (3'(y ? L2sb10 : s1bit_t'(1)) == 3'b110);
        assert (3'(y ? L2sb11 : s1bit_t'(1)) == 3'b111);

        assert (u3bit_t'(y ? L1b0   : s1bit_t'(1)) == 3'b000);
        assert (u3bit_t'(y ? L1b1   : s1bit_t'(1)) == 3'b001);
        assert (u3bit_t'(y ? L1sb0  : s1bit_t'(1)) == 3'b000);
        assert (u3bit_t'(y ? L1sb1  : s1bit_t'(1)) == 3'b111);
        assert (u3bit_t'(y ? L2b00  : s1bit_t'(1)) == 3'b000);
        assert (u3bit_t'(y ? L2b01  : s1bit_t'(1)) == 3'b001);
        assert (u3bit_t'(y ? L2b10  : s1bit_t'(1)) == 3'b010);
        assert (u3bit_t'(y ? L2b11  : s1bit_t'(1)) == 3'b011);
        assert (u3bit_t'(y ? L2sb00 : s1bit_t'(1)) == 3'b000);
        assert (u3bit_t'(y ? L2sb01 : s1bit_t'(1)) == 3'b001);
        assert (u3bit_t'(y ? L2sb10 : s1bit_t'(1)) == 3'b110);
        assert (u3bit_t'(y ? L2sb11 : s1bit_t'(1)) == 3'b111);

	assert (byte'(y ? L1b0   : s1bit_t'(1)) == 8'h00);
        assert (byte'(y ? L1b1   : s1bit_t'(1)) == 8'h01);
        assert (byte'(y ? L1sb0  : s1bit_t'(1)) == 8'h00);
        assert (byte'(y ? L1sb1  : s1bit_t'(1)) == 8'hff);
        assert (byte'(y ? L2b00  : s1bit_t'(1)) == 8'h00);
        assert (byte'(y ? L2b01  : s1bit_t'(1)) == 8'h01);
        assert (byte'(y ? L2b10  : s1bit_t'(1)) == 8'h02);
        assert (byte'(y ? L2b11  : s1bit_t'(1)) == 8'h03);
        assert (byte'(y ? L2sb00 : s1bit_t'(1)) == 8'h00);
        assert (byte'(y ? L2sb01 : s1bit_t'(1)) == 8'h01);
        assert (byte'(y ? L2sb10 : s1bit_t'(1)) == 8'hfe);
        assert (byte'(y ? L2sb11 : s1bit_t'(1)) == 8'hff);

        assert (int'(y ? L1b0   : s1bit_t'(1)) == 32'h0000_0000);
        assert (int'(y ? L1b1   : s1bit_t'(1)) == 32'h0000_0001);
        assert (int'(y ? L1sb0  : s1bit_t'(1)) == 32'h0000_0000);
        assert (int'(y ? L1sb1  : s1bit_t'(1)) == 32'hffff_ffff);
        assert (int'(y ? L2b00  : s1bit_t'(1)) == 32'h0000_0000);
        assert (int'(y ? L2b01  : s1bit_t'(1)) == 32'h0000_0001);
        assert (int'(y ? L2b10  : s1bit_t'(1)) == 32'h0000_0002);
        assert (int'(y ? L2b11  : s1bit_t'(1)) == 32'h0000_0003);
        assert (int'(y ? L2sb00 : s1bit_t'(1)) == 32'h0000_0000);
        assert (int'(y ? L2sb01 : s1bit_t'(1)) == 32'h0000_0001);
        assert (int'(y ? L2sb10 : s1bit_t'(1)) == 32'hffff_fffe);
        assert (int'(y ? L2sb11 : s1bit_t'(1)) == 32'hffff_ffff);

        assert (s12bit_packed_struct_t'(y ? L1b0   : s1bit_t'(1)) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1b1   : s1bit_t'(1)) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L1sb0  : s1bit_t'(1)) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L1sb1  : s1bit_t'(1)) == 12'hfff);
        assert (s12bit_packed_struct_t'(y ? L2b00  : s1bit_t'(1)) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2b01  : s1bit_t'(1)) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2b10  : s1bit_t'(1)) == 12'h002);
        assert (s12bit_packed_struct_t'(y ? L2b11  : s1bit_t'(1)) == 12'h003);
        assert (s12bit_packed_struct_t'(y ? L2sb00 : s1bit_t'(1)) == 12'h000);
        assert (s12bit_packed_struct_t'(y ? L2sb01 : s1bit_t'(1)) == 12'h001);
        assert (s12bit_packed_struct_t'(y ? L2sb10 : s1bit_t'(1)) == 12'hffe);
        assert (s12bit_packed_struct_t'(y ? L2sb11 : s1bit_t'(1)) == 12'hfff);

    end
endmodule
