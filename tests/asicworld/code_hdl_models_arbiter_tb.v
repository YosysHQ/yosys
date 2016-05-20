module testbench ();

reg             clk = 0;
reg             rst = 1;
reg             req3 = 0;
reg             req2 = 0;
reg             req1 = 0;
reg             req0 = 0;
wire            gnt3;   
wire            gnt2;   
wire            gnt1;   
wire            gnt0;  

// Clock generator
always #1 clk = ~clk;
integer file;

always @(posedge clk)
  $fdisplay(file, "%b", {gnt3, gnt2, gnt1, gnt0});

initial begin
  file = $fopen(`outfile);
  repeat (5) @ (posedge clk);
  rst <= 0;
  repeat (1) @ (posedge clk);
  req0 <= 1;
  repeat (1) @ (posedge clk);
  req0 <= 0;
  repeat (1) @ (posedge clk);
  req0 <= 1;
  req1 <= 1;
  repeat (1) @ (posedge clk);
  req2 <= 1;
  req1 <= 0;
  repeat (1) @ (posedge clk);
  req3 <= 1;
  req2 <= 0;
  repeat (1) @ (posedge clk);
  req3 <= 0;
  repeat (1) @ (posedge clk);
  req0 <= 0;
  repeat (1) @ (posedge clk);
  #10 $finish;
end 

// Connect the DUT
arbiter U (
 clk,    
 rst,    
 req3,   
 req2,   
 req1,   
 req0,   
 gnt3,   
 gnt2,   
 gnt1,   
 gnt0   
);

endmodule
