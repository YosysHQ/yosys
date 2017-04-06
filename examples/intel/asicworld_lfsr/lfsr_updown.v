`default_nettype none
module lfsr_updown (
clk       ,   // Clock input
reset     ,   // Reset input
enable    ,   // Enable input
up_down   ,   // Up Down input
count     ,   // Count output
overflow      // Overflow output
);

 input clk;
 input reset;
 input enable; 
 input up_down;

 output [7 : 0] count;
 output overflow;

 reg [7 : 0] count;

 assign overflow = (up_down) ? (count == {{7{1'b0}}, 1'b1}) : 
                               (count == {1'b1, {7{1'b0}}}) ;

 always @(posedge clk)
 if (reset) 
    count <= {7{1'b0}};
 else if (enable) begin
    if (up_down) begin
      count <= {~(^(count & 8'b01100011)),count[7:1]};
    end else begin
      count <= {count[5:0],~(^(count &  8'b10110001))};
    end
 end

endmodule
