
// test_parse2synthtrans_behavopt_1_test.v
module f1_test(in, out, clk, reset);
input in, reset;
output reg out;
input clk;
reg signed [3:0] a;
reg signed [3:0] b;
reg signed [3:0] c;
reg [5:0] d;
reg [5:0] e;

always @(clk or reset) begin
    a = -4;
    b = 2;
    c = a + b;
    d = a + b + c;
    d = d*d;
    if(b)
        e = d*d;
    else 
        e = d + d;
end
endmodule

// test_parse2synthtrans_case_1_test.v
module f2_demultiplexer1_to_4 (out0, out1, out2, out3, in, s1, s0);
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

// test_parse2synthtrans_contassign_1_test.v
module f3_test(in, out);

input wire in;
output  out;
assign out = (in+in);
assign out = 74;
endmodule

// test_parse2synthtrans_module_basic0_test.v
module f4_test;
endmodule

// test_parse2synthtrans_operators_1_test.v
module f5_test(in, out);
input in;
output out;
parameter p1 = 10;
parameter p2 = 5;

assign out = +p1;
assign out = -p2;
assign out = p1 + p2;
assign out = p1 - p2;
endmodule

// test_parse2synthtrans_param_1_test.v
module f6_test(in, out);
input in;
output out;
parameter p = 10;

assign out = p;
endmodule

// test_parse2synthtrans_port_scalar_1_test.v
module f7_test(in, out, io);
inout io;
output out;
input in;

endmodule

// test_parse2synthtrans_port_vector_1_test.v
module f8_test(in1, in2, out1, out2, io1, io2);
inout [1:0] io1;
inout [0:1] io2;
output [1:0] out1;
output [0:1] out2;
input [1:0] in1;
input [0:1] in2;

endmodule

// test_parse2synthtrans_v2k_comb_logic_sens_list_test.v
module f9_test(q, d, clk, reset);
output reg q;
input d, clk, reset;

always @ (posedge clk, negedge reset)
	if(!reset) q <= 0;
	else q <= d;

endmodule
