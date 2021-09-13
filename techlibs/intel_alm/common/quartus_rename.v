`ifdef cyclonev
`define LCELL cyclonev_lcell_comb
`define MAC cyclonev_mac
`define MLAB cyclonev_mlab_cell
`define IBUF cyclonev_io_ibuf
`define OBUF cyclonev_io_obuf
`define CLKENA cyclonev_clkena
`endif
`ifdef cyclone10gx
`define LCELL cyclone10gx_lcell_comb
`define MAC cyclone10gx_mac
`define MLAB cyclone10gx_mlab_cell
`define IBUF cyclone10gx_io_ibuf
`define OBUF cyclone10gx_io_obuf
`define CLKENA cyclone10gx_clkena
`endif

module __MISTRAL_VCC(output Q);

MISTRAL_ALUT2 #(.LUT(4'b1111)) _TECHMAP_REPLACE_ (.A(1'b1), .B(1'b1), .Q(Q));

endmodule


module __MISTRAL_GND(output Q);

MISTRAL_ALUT2 #(.LUT(4'b0000)) _TECHMAP_REPLACE_ (.A(1'b1), .B(1'b1), .Q(Q));

endmodule


module MISTRAL_FF(input DATAIN, CLK, ACLR, ENA, SCLR, SLOAD, SDATA, output reg Q);

dffeas #(.power_up("low"), .is_wysiwyg("true")) _TECHMAP_REPLACE_ (.d(DATAIN), .clk(CLK), .clrn(ACLR), .ena(ENA), .sclr(SCLR), .sload(SLOAD), .asdata(SDATA), .q(Q));

endmodule


module MISTRAL_ALUT6(input A, B, C, D, E, F, output Q);
parameter [63:0] LUT = 64'h0000_0000_0000_0000;

`LCELL #(.lut_mask(LUT)) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D), .datae(E), .dataf(F), .combout(Q));

endmodule


module MISTRAL_ALUT5(input A, B, C, D, E, output Q);
parameter [31:0] LUT = 32'h0000_0000;

`LCELL #(.lut_mask({2{LUT}})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D), .datae(E), .combout(Q));

endmodule


module MISTRAL_ALUT4(input A, B, C, D, output Q);
parameter [15:0] LUT = 16'h0000;

`LCELL #(.lut_mask({4{LUT}})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D), .combout(Q));

endmodule


module MISTRAL_ALUT3(input A, B, C, output Q);
parameter [7:0] LUT = 8'h00;

`LCELL #(.lut_mask({8{LUT}})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .combout(Q));

endmodule


module MISTRAL_ALUT2(input A, B, output Q);
parameter [3:0] LUT = 4'h0;

`LCELL #(.lut_mask({16{LUT}})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .combout(Q));

endmodule


module MISTRAL_NOT(input A, output Q);

NOT _TECHMAP_REPLACE_ (.IN(A), .OUT(Q));

endmodule


module MISTRAL_ALUT_ARITH(input A, B, C, D0, D1, CI, output SO, CO);
parameter LUT0 = 16'h0000;
parameter LUT1 = 16'h0000;

`LCELL #(.lut_mask({16'h0, LUT1, 16'h0, LUT0})) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D0), .dataf(D1), .cin(CI), .sumout(SO), .cout(CO));

endmodule


module MISTRAL_MLAB(input [4:0] A1ADDR, input A1DATA, A1EN, CLK1, input [4:0] B1ADDR, output B1DATA);

parameter _TECHMAP_CELLNAME_ = "";

// Here we get to an unfortunate situation. The cell has a mem_init0 parameter,
// which takes in a hexadecimal string that could be used to initialise RAM.
// In the vendor simulation models, this appears to work fine, but Quartus,
// either intentionally or not, forgets about this parameter and initialises the
// RAM to zero.
//
// Because of this, RAM initialisation is presently disabled, but the source
// used to generate mem_init0 is kept (commented out) in case this gets fixed
// or an undocumented way to get Quartus to initialise from mem_init0 is found.

`MLAB #(
    .logical_ram_name(_TECHMAP_CELLNAME_),
    .logical_ram_depth(32),
    .logical_ram_width(1),
    .mixed_port_feed_through_mode("Dont Care"),
    .first_bit_number(0),
    .first_address(0),
    .last_address(31),
    .address_width(5),
    .data_width(1),
    .byte_enable_mask_width(1),
    .port_b_data_out_clock("NONE"),
    // .mem_init0($sformatf("%08x", INIT))
) _TECHMAP_REPLACE_ (
    .portaaddr(A1ADDR),
    .portadatain(A1DATA),
    .portbaddr(B1ADDR),
    .portbdataout(B1DATA),
    .ena0(A1EN),
    .clk0(CLK1)
);

endmodule


module MISTRAL_M10K(A1ADDR, A1DATA, A1EN, CLK1, B1ADDR, B1DATA, B1EN);

parameter CFG_ABITS = 10;
parameter CFG_DBITS = 10;

parameter _TECHMAP_CELLNAME_ = "";

input [CFG_ABITS-1:0] A1ADDR, B1ADDR;
input [CFG_DBITS-1:0] A1DATA;
input CLK1, A1EN, B1EN;
output [CFG_DBITS-1:0] B1DATA;

// Much like the MLAB, the M10K has mem_init[01234] parameters which would let
// you initialise the RAM cell via hex literals. If they were implemented.

cyclonev_ram_block #(
    .operation_mode("dual_port"),
    .logical_ram_name(_TECHMAP_CELLNAME_),
    .port_a_address_width(CFG_ABITS),
    .port_a_data_width(CFG_DBITS),
    .port_a_logical_ram_depth(2**CFG_ABITS),
    .port_a_logical_ram_width(CFG_DBITS),
    .port_a_first_address(0),
    .port_a_last_address(2**CFG_ABITS - 1),
    .port_a_first_bit_number(0),
    .port_b_address_width(CFG_ABITS),
    .port_b_data_width(CFG_DBITS),
    .port_b_logical_ram_depth(2**CFG_ABITS),
    .port_b_logical_ram_width(CFG_DBITS),
    .port_b_first_address(0),
    .port_b_last_address(2**CFG_ABITS - 1),
    .port_b_first_bit_number(0),
    .port_b_address_clock("clock0"),
    .port_b_read_enable_clock("clock0")
) _TECHMAP_REPLACE_ (
    .portaaddr(A1ADDR),
    .portadatain(A1DATA),
    .portawe(A1EN),
    .portbaddr(B1ADDR),
    .portbdataout(B1DATA),
    .portbre(B1EN),
    .clk0(CLK1)
);

endmodule


module MISTRAL_MUL27X27(input [26:0] A, B, output [53:0] Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;

`MAC #(
    .ax_width(27),
    .signed_max(A_SIGNED ? "true" : "false"),
    .ay_scan_in_width(27),
    .signed_may(B_SIGNED ? "true" : "false"),
    .result_a_width(54),
    .operation_mode("M27x27")
) _TECHMAP_REPLACE_ (
    .ax(A),
    .ay(B),
    .resulta(Y)
);

endmodule


module MISTRAL_MUL18X18(input [17:0] A, B, output [35:0] Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;

`MAC #(
    .ax_width(18),
    .signed_max(A_SIGNED ? "true" : "false"),
    .ay_scan_in_width(18),
    .signed_may(B_SIGNED ? "true" : "false"),
    .result_a_width(36),
    .operation_mode("M18x18_FULL")
) _TECHMAP_REPLACE_ (
    .ax(A),
    .ay(B),
    .resulta(Y)
);

endmodule


module MISTRAL_MUL9X9(input [8:0] A, B, output [17:0] Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;

`MAC #(
    .ax_width(9),
    .signed_max(A_SIGNED ? "true" : "false"),
    .ay_scan_in_width(9),
    .signed_may(B_SIGNED ? "true" : "false"),
    .result_a_width(18),
    .operation_mode("M9x9")
) _TECHMAP_REPLACE_ (
    .ax(A),
    .ay(B),
    .resulta(Y)
);

endmodule

module MISTRAL_IB(input PAD, output O);
`IBUF #(
    .bus_hold("false"),
    .differential_mode("false")
) _TECHMAP_REPLACE_ (
    .i(PAD),
    .o(O)
);
endmodule

module MISTRAL_OB(output PAD, input I, OE);
`OBUF #(
    .bus_hold("false"),
    .differential_mode("false")
) _TECHMAP_REPLACE_ (
    .i(I),
    .o(PAD),
    .oe(OE)
);
endmodule

module MISTRAL_IO(output PAD, input I, OE, output O);
`IBUF #(
    .bus_hold("false"),
    .differential_mode("false")
) ibuf (
    .i(PAD),
    .o(O)
);

`OBUF #(
    .bus_hold("false"),
    .differential_mode("false")
) obuf (
    .i(I),
    .o(PAD),
    .oe(OE)
);
endmodule

module MISTRAL_CLKBUF (input A, output Q);
`CLKENA #(
    .clock_type("auto"),
    .ena_register_mode("always enabled"),
    .ena_register_power_up("high"),
    .disable_mode("low"),
    .test_syn("high")
) _TECHMAP_REPLACE_ (
    .inclk(A),
    .ena(1'b1),
    .outclk(Q)
);
endmodule
