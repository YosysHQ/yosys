module sevenseg ( output reg [6:0] HEX0,
                  input      [3:0] SW );

   always @(*) begin
     case(SW)
        4'h1: HEX0 = 7'b1111001;
	4'h2: HEX0 = 7'b0100100;
	4'h3: HEX0 = 7'b0110000;
	4'h4: HEX0 = 7'b0011001;
	4'h5: HEX0 = 7'b0010010;
	4'h6: HEX0 = 7'b0000010;
	4'h7: HEX0 = 7'b1111000;
	4'h8: HEX0 = 7'b0000000;
	4'h9: HEX0 = 7'b0011000;
	4'ha: HEX0 = 7'b0001000;
	4'hb: HEX0 = 7'b0000011;
	4'hc: HEX0 = 7'b1000110;
	4'hd: HEX0 = 7'b0100001;
	4'he: HEX0 = 7'b0000110;
	4'hf: HEX0 = 7'b0001110;
	4'h0: HEX0 = 7'b1000000;
     endcase // case (SW)
   end

endmodule
