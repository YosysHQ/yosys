module demo(input clk, reset, ctrl);
  localparam NBITS = 10;
  reg [NBITS-1:0] counter;
  initial counter[NBITS-2] = 0;
  initial counter[0] = 1;
  always @(posedge clk) begin
    counter <= reset ? 1 : ctrl ? counter + 1 : counter - 1;
    assume(counter != 0);
    assume(counter != 1 << (NBITS-1));
    assert(counter != (1 << NBITS)-1);
  end
endmodule
