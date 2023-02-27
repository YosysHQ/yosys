module top (
	input clk,
	input [5:0] currentstate,
	output reg [1:0] o
	);
	always @ (posedge clk)
	begin
		case (currentstate)
			5'd1,5'd2, 5'd3: 
				begin 
					o <= 2'b01;
				end	
			5'd4:
			  	begin
					o <= 2'b10;
				end
			5'd5,5'd6,5'd7: 
				begin
					o <= 2'b11;
				end
			default :
				begin
					o <= 2'b00;
				end
		endcase
	end
endmodule

