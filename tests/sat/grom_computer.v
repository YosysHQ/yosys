module grom_computer
  (input  clk,     // Main Clock
   input  reset,   // reset
   output hlt,
   output reg[7:0] display_out
  );

 wire [11:0] addr;
 wire [7:0] memory_out;
 wire [7:0] memory_in;
 wire mem_enable;
 wire  we;
 wire ioreq;

 grom_cpu cpu(.clk(clk),.reset(reset),.addr(addr),.data_in(memory_out),.data_out(memory_in),.we(we),.ioreq(ioreq),.hlt(hlt));

 assign mem_enable = we & ~ioreq;

 ram_memory memory(.clk(clk),.addr(addr),.data_in(memory_in),.we(mem_enable),.data_out(memory_out));

 always @(posedge clk)
	begin
		if(ioreq==1 && we==1)
		begin
			display_out <= memory_in;
			`ifdef DISASSEMBLY
			$display("Display output : %h", memory_in);
			`endif
		end
	end
endmodule
