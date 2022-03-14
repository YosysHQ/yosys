module ram_memory(
  input clk,
  input [11:0] addr,
  input [7:0] data_in,
  input we,
  output reg [7:0] data_out
);

  reg [7:0] store[0:4095] /* verilator public_flat */;

  initial
  begin
	store[0] <= 8'b11100001; // MOV DS,2
	store[1] <= 8'b00000010; //
	store[2] <= 8'b01010100; // LOAD R1,[R0]
	store[3] <= 8'b00110001; // INC R1
	store[4] <= 8'b00110001; // INC R1
	store[5] <= 8'b01100001; // STORE [R0],R1
	store[6] <= 8'b11010001; // OUT [0],R1
	store[7] <= 8'b00000000; //
	store[8] <= 8'b00110001; // INC R1
	store[9] <= 8'b10100001; // CALL 0x100
	store[10] <= 8'b00000000; //
	store[11] <= 8'b01111111; // HLT


	store[256] <= 8'b11010001; // OUT [0],R1
	store[257] <= 8'b00000000; //
	store[258] <= 8'b01111110; // RET

	store[512] <= 8'b00000000;
  end

  always @(posedge clk)
	if (we)
	  store[addr] <= data_in;
	else
	  data_out <= store[addr];
endmodule
