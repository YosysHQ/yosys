`ifdef cyclonev
`define LCELL cyclonev_lcell_comb
`define MLAB cyclonev_mlab_cell
`endif
`ifdef cyclone10gx
`define LCELL cyclone10gx_lcell_comb
`define MLAB cyclone10gx_mlab_cell
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
    .logical_ram_name("MISTRAL_MLAB"),
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
