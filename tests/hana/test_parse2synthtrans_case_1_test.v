module demultiplexer1_to_4 (out0, out1, out2, out3, in, s1, s0);
output out0, out1, out2, out3;
reg out0, out1, out2, out3;
input in;
input s1, s0;
reg [3:0] encoding;
reg [1:0] state;
   always @(encoding) begin
        case (encoding)
        4'bxx11: state = 1;
        4'bx0xx: state = 3;
        4'b11xx: state = 4;
        4'bx1xx: state = 2;
        4'bxx1x: state = 1;
        4'bxxx1: state = 0;
        default: state = 0;
        endcase
   end
   
   always @(encoding) begin
        case (encoding)
        4'b0000: state = 1;
        default: state = 0;
        endcase
   end
endmodule
