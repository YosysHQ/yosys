//  Xilinx UltraRAM Single Port Read First Mode.  This code implements
//  a parameterizable UltraRAM block in read first mode. The behavior of this RAM is
//  when data is written, the old memory contents at the write address are
//  presented on the output port.
//
module xilinx_ultraram_single_port_read_first #(

//Default parameters were changed because of slow test
  //parameter AWIDTH = 12,  // Address Width
  //parameter DWIDTH = 72,  // Data Width
  //parameter NBPIPE = 3    // Number of pipeline Registers
  parameter AWIDTH = 8,  // Address Width
  parameter DWIDTH = 8,  // Data Width
  parameter NBPIPE = 3    // Number of pipeline Registers
 ) (
    input clk,                    // Clock
    input rst,                    // Reset
    input we,                     // Write Enable
    input regce,                  // Output Register Enable
    input mem_en,                 // Memory Enable
    input [DWIDTH-1:0] din,       // Data Input
    input [AWIDTH-1:0] addr,      // Address Input
    output reg [DWIDTH-1:0] dout  // Data Output
   );

(* ram_style = "ultra" *)
reg [DWIDTH-1:0] mem[(1<<AWIDTH)-1:0];        // Memory Declaration
reg [DWIDTH-1:0] memreg;
reg [DWIDTH-1:0] mem_pipe_reg[NBPIPE-1:0];    // Pipelines for memory
reg mem_en_pipe_reg[NBPIPE:0];                // Pipelines for memory enable

integer          i;

// RAM : Both READ and WRITE have a latency of one
always @ (posedge clk)
begin
 if(mem_en)
  begin
   if(we)
    mem[addr] <= din;
   memreg <= mem[addr];
  end
end

// The enable of the RAM goes through a pipeline to produce a
// series of pipelined enable signals required to control the data
// pipeline.
always @ (posedge clk)
begin
 mem_en_pipe_reg[0] <= mem_en;
 for (i=0; i<NBPIPE; i=i+1)
   mem_en_pipe_reg[i+1] <= mem_en_pipe_reg[i];
end

// RAM output data goes through a pipeline.
always @ (posedge clk)
begin
 if (mem_en_pipe_reg[0])
  mem_pipe_reg[0] <= memreg;
end

always @ (posedge clk)
begin
 for (i = 0; i < NBPIPE-1; i = i+1)
  if (mem_en_pipe_reg[i+1])
   mem_pipe_reg[i+1] <= mem_pipe_reg[i];
end

// Final output register gives user the option to add a reset and
// an additional enable signal just for the data ouptut
always @ (posedge clk)
begin
 if (rst)
   dout <= 0;
 else if (mem_en_pipe_reg[NBPIPE] && regce)
   dout <= mem_pipe_reg[NBPIPE-1];
end
endmodule
