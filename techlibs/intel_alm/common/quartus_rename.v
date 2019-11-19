module __MISTRAL_VCC(output Q);

MISTRAL_ALUT2 #(.LUT(4'b1111)) _TECHMAP_REPLACE_ (.A(1'b1), .B(1'b1), .Q(Q));

endmodule


module __MISTRAL_GND(output Q);

MISTRAL_ALUT2 #(.LUT(4'b0000)) _TECHMAP_REPLACE_ (.A(1'b1), .B(1'b1), .Q(Q));

endmodule


module MISTRAL_FF(input D, CLK, ACn, ALD, AD, EN, output reg Q);

parameter INIT = 1'b0;

localparam [1023:0] INIT_STR = (INIT !== 1'b1) ? "low" : "high";

dffeas #(.power_up(INIT_STR), .is_wysiwyg("true")) _TECHMAP_REPLACE_ (.d(D), .clk(CLK), .clrn(ACn), .aload(ALD), .asdata(AD), .ena(EN), .q(Q));

endmodule
