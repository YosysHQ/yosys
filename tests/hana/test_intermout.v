
// test_intermout_always_comb_1_test.v
module f1_test(a, b, c, d, z);
input a, b, c, d;
output z;
reg z, temp1, temp2;

always @(a or b or c or d)
begin
    temp1 = a ^ b;
	temp2 = c ^ d;
	z = temp1 ^ temp2;
end	

endmodule

// test_intermout_always_comb_3_test.v
module f2_test (in1, in2, out);
input  in1, in2;
output  reg out;

always @ ( in1 or in2)
	if(in1 > in2)
		out = in1;
	else
		out = in2;
endmodule		

// test_intermout_always_comb_4_test.v
module f3_test(a, b, c);
input b, c;
output reg a;

always @(b or c) begin
a = b;
a = c;
end
endmodule

// test_intermout_always_comb_5_test.v
module f4_test(ctrl, in1,  in2, out);
input ctrl;
input  in1, in2;
output  reg out;

always @ (ctrl or in1 or in2)
	if(ctrl)
		out = in1 & in2;
	else 
		out = in1 | in2;
endmodule		

// test_intermout_always_ff_3_test.v
module f5_NonBlockingEx(clk, merge, er, xmit, fddi, claim);
input clk, merge, er, xmit, fddi;
output reg claim;
reg fcr;

always @(posedge clk)
begin
    fcr = er | xmit;

	if(merge)
	    claim = fcr & fddi;
	else
	    claim = fddi;
end
endmodule

// test_intermout_always_ff_4_test.v
module f6_FlipFlop(clk, cs, ns);
input clk;
input [31:0] cs;
output [31:0] ns;
integer is;

always @(posedge clk)
    is <= cs;

assign ns = is;
endmodule	

// test_intermout_always_ff_5_test.v
module f7_FlipFlop(clock, cs, ns);
input clock;
input [3:0] cs;
output reg [3:0] ns;
reg [3:0] temp;

always @(posedge clock)
begin
    temp = cs;
	ns = temp;
end	

endmodule	

// test_intermout_always_ff_6_test.v
module f8_inc(clock, counter);

input clock;
output reg [3:0] counter;
always @(posedge clock)
	counter <= counter + 1;
endmodule	

// test_intermout_always_ff_8_test.v
module f9_NegEdgeClock(q, d, clk, reset);
input d, clk, reset;
output reg q;

always @(negedge clk or negedge reset)
    if(!reset)
	    q <= 1'b0;
	else	
        q <= d;

endmodule

// test_intermout_always_ff_9_test.v
module f10_MyCounter (clock, preset, updown, presetdata, counter);
input clock, preset, updown;
input [1: 0] presetdata;
output reg [1:0] counter;

always @(posedge clock)
    if(preset)
	    counter <= presetdata;
	else
	    if(updown)
		    counter <= counter + 1;
		else
		    counter <= counter - 1;
endmodule			

// test_intermout_always_latch_1_test.v
module f11_test(en, in, out);
input en;
input [1:0] in;
output reg [2:0] out;

always @ (en or in)
	if(en)
		out = in + 1;
endmodule		

// test_intermout_bufrm_1_test.v
module f12_test(input in, output out);
//no buffer removal
assign out = in;
endmodule

// test_intermout_bufrm_2_test.v
module f13_test(input in, output out);
//intermediate buffers should be removed
wire w1, w2;
assign w1 = in;
assign w2 = w1;
assign out = w2;
endmodule

// test_intermout_bufrm_6_test.v
module f14_test(in, out);
input in;
output out;

wire w1, w2, w3, w4;
assign w1 = in;
assign w2 = w1;
assign w4 = w3;
assign out = w4;
f14_mybuf _f14_mybuf(w2, w3);
endmodule

module f14_mybuf(in, out);
input in;
output out;
wire w1, w2, w3, w4;

assign w1 = in;
assign w2 = w1;
assign out = w2;
endmodule


// test_intermout_bufrm_7_test.v
module f15_test(in1, in2, out);
input in1, in2;
output out;
// Y with cluster of f15_mybuf instances at the junction

wire w1, w2, w3, w4, w5, w6, w7, w8, w9, w10;
assign w1 = in1;
assign w2 = w1;
assign w5 = in2;
assign w6 = w5;
assign w10 = w9;
assign out = w10;

f15_mybuf _f15_mybuf0(w2, w3);
f15_mybuf _f15_mybuf1(w3, w4);

f15_mybuf _f15_mybuf2(w6, w7);
f15_mybuf _f15_mybuf3(w7, w4);

f15_mybuf _f15_mybuf4(w4, w8);
f15_mybuf _f15_mybuf5(w8, w9);
endmodule

module f15_mybuf(in, out);
input in;
output out;
wire w1, w2, w3, w4;

assign w1 = in;
assign w2 = w1;
assign out = w2;
endmodule


// test_intermout_exprs_add_test.v
module f16_test(out, in1, in2, vin1, vin2, vout1);
output out;
input in1, in2;
input [1:0] vin1;
input [2:0] vin2;
output [3:0] vout1;

assign out = in1 + in2;
assign vout1 = vin1 + vin2;
endmodule

// test_intermout_exprs_binlogic_test.v
module f17_test(in1, in2, vin1, vin2, out, vout, vin3, vin4, vout1 );
input in1, in2;
input [1:0] vin1;
input [3:0] vin2;
input [1:0] vin3;
input [3:0] vin4;
output vout, vout1;
output out;

assign out = in1 && in2;
assign vout = vin1 && vin2;
assign vout1 = vin3 || vin4;
endmodule

// test_intermout_exprs_bitwiseneg_test.v
module f18_test(output out, input in, output [1:0] vout, input [1:0] vin);

assign out = ~in;
assign vout = ~vin;
endmodule

// test_intermout_exprs_buffer_test.v
module f19_buffer(in, out, vin, vout);
input  in;
output out;
input [1:0] vin;
output [1:0] vout;

assign out = in;
assign vout = vin;
endmodule

// test_intermout_exprs_condexpr_mux_test.v
module f20_test(in1, in2, out,  vin1, vin2, vin3, vin4, vout1, vout2, en1, ven1, ven2);
input in1, in2, en1, ven1;
input [1:0] ven2;
output out;
input [1:0] vin1,  vin2, vin3, vin4;
output [1:0] vout1, vout2;

assign out = en1 ? in1 : in2;
assign vout1 = ven1 ? vin1 : vin2;
assign vout2 = ven2 ? vin3 : vin4;
endmodule

// test_intermout_exprs_condexpr_tribuf_test.v
module f21_test(in, out, en, vin1, vout1, en1);
input in, en, en1;
output out;
input [1:0] vin1;
output [1:0] vout1;

assign out = en ? in : 1'bz;
assign vout1 = en1 ? vin1 : 2'bzz;
endmodule

// test_intermout_exprs_constshift_test.v
module f22_test(in, out, vin, vout, vin1, vout1, vin2, vout2);

input in;
input [3:0] vin, vin1, vin2;
output [3:0] vout, vout1, vout2;
output out;

assign out = in << 1;
assign vout = vin << 2;
assign vout1 = vin1 >> 2;
assign vout2 = vin2 >>> 2;
endmodule

// test_intermout_exprs_const_test.v
module f23_test (out, vout);
output out;
output [7:0] vout;

assign out = 1'b1;
assign vout = 9;
endmodule

// test_intermout_exprs_div_test.v
module f24_test(out, in1, in2, vin1, vin2, vout1);
output out;
input in1, in2;
input [1:0] vin1;
input [2:0] vin2;
output [3:0] vout1;

assign out = in1 / in2;
assign vout1 = vin1 / vin2;
endmodule

// test_intermout_exprs_logicneg_test.v
module f25_test(out, vout, in, vin);
output out, vout;
input in;
input [3:0] vin;
assign out = !in;
assign vout = !vin;
endmodule

// test_intermout_exprs_mod_test.v
module f26_test(out, in1, in2, vin1, vin2, vout1);
output out;
input in1, in2;
input [1:0] vin1;
input [2:0] vin2;
output [3:0] vout1;

assign out = in1 % in2;
assign vout1 = vin1 % vin2;
endmodule

// test_intermout_exprs_mul_test.v
module f27_test(out, in1, in2, vin1, vin2, vout1);
output out;
input in1, in2;
input [1:0] vin1;
input [2:0] vin2;
output [3:0] vout1;

assign out = in1 * in2;
assign vout1 = vin1 * vin2;
endmodule

// test_intermout_exprs_redand_test.v
module f28_test(output out, input [1:0] vin, output out1, input [3:0] vin1);

assign out = &vin;
assign out1 = &vin1;
endmodule

// test_intermout_exprs_redop_test.v
module f29_Reduction (A1, A2, A3, A4, A5, A6, Y1, Y2, Y3, Y4, Y5, Y6);
input [1:0] A1; 
input [1:0] A2; 
input [1:0] A3; 
input [1:0] A4; 
input [1:0] A5; 
input [1:0] A6; 
output Y1, Y2, Y3, Y4, Y5, Y6; 
//reg Y1, Y2, Y3, Y4, Y5, Y6; 
assign Y1=&A1; //reduction AND 
assign Y2=|A2; //reduction OR 
assign Y3=~&A3; //reduction NAND 
assign Y4=~|A4; //reduction NOR 
assign Y5=^A5; //reduction XOR 
assign Y6=~^A6; //reduction XNOR 
endmodule

// test_intermout_exprs_sub_test.v
module f30_test(out, in1, in2, vin1, vin2, vout1);
output out;
input in1, in2;
input [1:0] vin1;
input [2:0] vin2;
output [3:0] vout1;

assign out = in1 - in2;
assign vout1 = vin1 - vin2;
endmodule

// test_intermout_exprs_unaryminus_test.v
module f31_test(output out, input in, output [31:0] vout, input [31:0] vin);

assign out = -in;
assign vout = -vin;
endmodule

// test_intermout_exprs_unaryplus_test.v
module f32_test(output out, input in);

assign out = +in;
endmodule

// test_intermout_exprs_varshift_test.v
module f33_test(vin0, vout0);
input [2:0] vin0;
output reg [7:0] vout0;

wire [7:0] myreg0, myreg1, myreg2;
integer i;
assign myreg0 = vout0 << vin0;

assign myreg1 = myreg2 >> i;
endmodule
