`timescale 1ns/10ps

module svinterface1_tb;


  logic clk;
  logic rst;
  logic [21:0] outOther;
  logic [1:0] sig;
  logic [1:0] sig_out;
  logic flip;
  logic [15:0] passThrough;
  integer outfile;

  TopModule u_dut (
    .clk(clk),
    .rst(rst),
    .outOther(outOther),
    .sig(sig),
    .flip(flip),
    .passThrough(passThrough),
    .sig_out(sig_out)
  );

  initial begin
    clk = 0;
    while(1) begin
      clk = ~clk;
      #50;
    end
  end

  initial begin
    outfile = $fopen("output.txt");
    rst = 1;
    sig = 0;
    flip = 0;
    @(posedge clk);
    #(2);
    rst = 0;
    @(posedge clk);
    for(int j=0;j<2;j++) begin
      for(int i=0;i<20;i++) begin
        #(2);
        flip = j;
        sig = i;
        @(posedge clk);
      end
    end
    $finish;
  end

  always @(negedge clk) begin
    $fdisplay(outfile, "%d %d %d", outOther, sig_out, passThrough);
  end

endmodule
