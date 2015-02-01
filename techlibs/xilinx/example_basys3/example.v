module example(CLK, LD);
  input CLK;
  output [15:0] LD;

  wire clock;
  reg [15:0] leds;

  BUFG CLK_BUF (.I(CLK), .O(clock));
  OBUF LD_BUF[15:0] (.I(leds), .O(LD));

  parameter COUNTBITS = 26;
  reg [COUNTBITS-1:0] counter;

  always @(posedge CLK) begin
    counter <= counter + 1;
    if (counter[COUNTBITS-1])
      leds <= 16'h8000 >> counter[COUNTBITS-2:COUNTBITS-5];
    else
      leds <= 16'h0001 << counter[COUNTBITS-2:COUNTBITS-5];
  end
endmodule
