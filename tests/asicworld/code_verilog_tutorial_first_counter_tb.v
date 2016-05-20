module testbench();
// Declare inputs as regs and outputs as wires
reg clock = 1, reset = 0, enable = 0;
wire [3:0] counter_out;
integer file;

// Initialize all variables
initial begin        
  file = $fopen(`outfile);
  $fdisplay (file, "time\t clk reset enable counter");	
  #5 reset = 1;    // Assert the reset
  #10 reset = 0;   // De-assert the reset
  #10 enable = 1;  // Assert enable
  #100 enable = 0; // De-assert enable
  #5 $finish;      // Terminate simulation
end

always @(negedge clock)
  $fdisplay (file, "%g\t %b   %b     %b      %b", 
	  $time, clock, reset, enable, counter_out);	

// Clock generator
initial begin
  #1;
  forever
    #5 clock = ~clock; // Toggle clock every 5 ticks
end

// Connect DUT to test bench
first_counter U_counter (
clock,
reset,
enable,
counter_out
);

endmodule
