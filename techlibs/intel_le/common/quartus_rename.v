`ifdef cycloneiv 
`define LCELL cycloneiv_lcell_comb
`define MAC cycloneiv_mac
`define MLAB cycloneiv_mlab_cell
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




module MISTRAL_ALUT4(input A, B, C, D, output Q);
parameter [15:0] LUT = 16'h0000;
parameter sum_lutc_input = "datac";
`LCELL #(.lut_mask(LUT),.sum_lutc_input(sum_lutc_input)) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D), .combout(Q));

endmodule


module MISTRAL_ALUT3(input A, B, C, output Q);
parameter [7:0] LUT = 8'h00;
parameter sum_lutc_input = "datac";
`LCELL #(.lut_mask({2{LUT}}),.sum_lutc_input(sum_lutc_input)) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .combout(Q));

endmodule


module MISTRAL_ALUT2(input A, B, output Q);
parameter [3:0] LUT = 4'h0;
parameter sum_lutc_input = "datac";
`LCELL #(.lut_mask({4{LUT}}),.sum_lutc_input(sum_lutc_input)) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .combout(Q));

endmodule


module MISTRAL_NOT(input A, output Q);

NOT _TECHMAP_REPLACE_ (.IN(A), .OUT(Q));

endmodule


module MISTRAL_ALUT_ARITH(input A, B, C, D, CI, output SO, CO);
parameter LUT = 16'h0000;
parameter sum_lutc_input = "datac";
`LCELL #(.lut_mask({LUT}),.sum_lutc_input(sum_lutc_input)) _TECHMAP_REPLACE_ (.dataa(A), .datab(B), .datac(C), .datad(D), .cin(CI), .sumout(SO), .cout(CO));

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


module MISTRAL_M9K(A1ADDR, A1DATA, A1EN, CLK1, B1ADDR, B1DATA, B1EN);

parameter CFG_ABITS = 10;
parameter CFG_DBITS = 10;

parameter _TECHMAP_CELLNAME_ = "";

input [CFG_ABITS-1:0] A1ADDR, B1ADDR;
input [CFG_DBITS-1:0] A1DATA;
input CLK1, A1EN, B1EN;
output [CFG_DBITS-1:0] B1DATA;

// Much like the MLAB, the M9K has mem_init[01234] parameters which would let
// you initialise the RAM cell via hex literals. If they were implemented.

cycloneiv_ram_block #(
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


