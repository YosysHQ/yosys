module MULT_32BIT (Amult, Bmult, Valid_mult, Cmult); 

input [31:0] Amult;
input [31:0] Bmult;
input  Valid_mult;
output [63:0] Cmult;

wire [1:0] valit_int;

assign valit_int = {Valid_mult,Valid_mult};

//qlal4s3_mult_cell_macro
qlal4s3_mult_cell_macro u_qlal4s3_mult_cell_macro 
												( 
													.Amult			(Amult), 
													.Bmult			(Bmult), 
													.Valid_mult		(valit_int),
													.sel_mul_32x32  (1'b1),							
													.Cmult			(Cmult)
												);

endmodule


