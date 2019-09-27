/** small, meaningless design to test loading of liberty files */

module small
(
    input clk,
    output reg[7:0] count
);

initial count = 0;

always @ (posedge clk) 
begin
    count <= count + 1'b1;
end

endmodule
