
module blocking_cond (in, out);

input in;
output reg out;
reg tmp;

always @* begin
	tmp = 1;
	out = 1'b0;
	case (1'b1)
		tmp: out = in;
	endcase
	tmp = 0;
end

endmodule

// -------------------------------------------------------------

module uut(clk, arst, a, b, c, d, e, f,  out1);

input clk, arst, a, b, c, d, e, f;
output reg [3:0] out1;

always @(posedge clk, posedge arst) begin
	if (arst)
		out1 = 0;
	else begin
		if (a) begin
			case ({b, c})
				2'b00:
					out1 = out1 + 9;
				2'b01, 2'b10:
					out1 = out1 + 13;
			endcase
			if (d) begin
				out1 = out1 + 2;
				out1 = out1 + 1;
			end
			case ({e, f})
				2'b11:
					out1 = out1 + 8;
				2'b00:
					;
				default:
					out1 = out1 + 10;
			endcase
			out1 = out1 ^ 7;
		end
		out1 = out1 + 14;
	end
end

endmodule

// -------------------------------------------------------------

// extracted from ../asicworld/code_hdl_models_uart.v
// (triggered a bug in the proc_mux pass)
module uart (reset, txclk, ld_tx_data, tx_empty, tx_cnt);

input reset;
input txclk;
input ld_tx_data;

output reg tx_empty;
output reg [3:0] tx_cnt;

always @ (posedge txclk)
if (reset) begin
  tx_empty      <= 1;
  tx_cnt        <= 0;
end else begin
   if (ld_tx_data) begin
     tx_empty <= 0;
   end
   if (!tx_empty) begin
     tx_cnt <= tx_cnt + 1;
   end
end

endmodule

