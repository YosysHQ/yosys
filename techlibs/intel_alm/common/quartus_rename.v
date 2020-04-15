module __MISTRAL_VCC(output Q);

MISTRAL_ALUT2 #(.LUT(4'b1111)) _TECHMAP_REPLACE_ (.A(1'b1), .B(1'b1), .Q(Q));

endmodule


module __MISTRAL_GND(output Q);

MISTRAL_ALUT2 #(.LUT(4'b0000)) _TECHMAP_REPLACE_ (.A(1'b1), .B(1'b1), .Q(Q));

endmodule


module MISTRAL_FF(input DATAIN, CLK, ACLR, ENA, SCLR, SLOAD, SDATA, output reg Q);

dffeas #(.power_up("low"), .is_wysiwyg("true")) _TECHMAP_REPLACE_ (.d(DATAIN), .clk(CLK), .clrn(ACLR), .ena(ENA), .sclr(SCLR), .sload(SLOAD), .asdata(SDATA), .q(Q));

endmodule
