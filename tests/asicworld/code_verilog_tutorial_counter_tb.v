///////////////////////////////////////////////////////////////////////////
// MODULE               : counter_tb                                     //
// TOP MODULE           : --                                             //
//                                                                       //
// PURPOSE              : 4-bit up counter test bench                    //
//                                                                       //
// DESIGNER             : Deepak Kumar Tala                              //
//                                                                       //
// Revision History                                                      //
//                                                                       //
// DEVELOPMENT HISTORY  :                                                //
//               Rev0.0 : Jan 03, 2003                                   //
//                        Initial Revision                               //
//                                                                       //
///////////////////////////////////////////////////////////////////////////
module testbench;

integer file;
reg clk = 0, reset = 0, enable = 0;
wire [3:0] count;
reg dut_error = 0;

counter U0 (
.clk    (clk),
.reset  (reset),
.enable (enable),
.count  (count)
);

event reset_enable;
event terminate_sim;

initial
 file = $fopen(`outfile);

always
  #5 clk = !clk;

initial
@ (terminate_sim)  begin
 $fdisplay (file, "Terminating simulation");
 if (dut_error == 0) begin
   $fdisplay (file, "Simulation Result : PASSED");
 end
 else begin
   $fdisplay (file, "Simulation Result : FAILED");
 end
 $fdisplay (file, "###################################################");
 #1 $finish;
end



event reset_done;

initial
forever begin
 @ (reset_enable);
 @ (negedge clk)
 $fdisplay (file, "Applying reset");
   reset = 1;
 @ (negedge clk)
   reset = 0;
 $fdisplay (file, "Came out of Reset");
 -> reset_done;
end

initial begin
  #10 -> reset_enable;
  @ (reset_done);
  @ (negedge clk);
  enable = 1;
  repeat (5)
  begin
   @ (negedge clk);
  end
  enable = 0;
  #5 -> terminate_sim;
end


reg [3:0] count_compare;

always @ (posedge clk)
if (reset == 1'b1)
 count_compare <= 0;
else if ( enable == 1'b1)
 count_compare <= count_compare + 1;



always @ (negedge clk)
if (count_compare != count) begin
  $fdisplay (file, "DUT ERROR AT TIME%d",$time);
  $fdisplay (file, "Expected value %d, Got Value %d", count_compare, count);
  dut_error = 1;
  #5 -> terminate_sim;
end

endmodule

