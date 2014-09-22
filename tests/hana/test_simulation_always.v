
// test_simulation_always_15_test.v
module f1_test(input [1:0] in, output reg [1:0] out);

always @(in)
    out = in;
endmodule	

// test_simulation_always_17_test.v
module f2_test(a, b, c, d, z);
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

// test_simulation_always_18_test.v
module f3_test (in1, in2, out);
input  in1, in2;
output  reg out;

always @ ( in1 or in2)
	if(in1 > in2)
		out = in1;
	else
		out = in2;
endmodule		

// test_simulation_always_19_test.v
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

// test_simulation_always_1_test.v
module f5_test(input in, output reg out);

always @(in)
    out = in;
endmodule	

// test_simulation_always_20_test.v
module f6_NonBlockingEx(clk, merge, er, xmit, fddi, claim);
input clk, merge, er, xmit, fddi;
output reg claim;
reg fcr;

always @(posedge clk)
begin
    fcr <= er | xmit;

	if(merge)
	    claim <= fcr & fddi;
	else
	    claim <= fddi;
end
endmodule

// test_simulation_always_21_test.v
module f7_FlipFlop(clk, cs, ns);
input clk;
input [7:0] cs;
output [7:0] ns;
integer is;

always @(posedge clk)
    is <= cs;

assign ns = is;
endmodule	

// test_simulation_always_22_test.v
module f8_inc(clock, counter);

input clock;
output reg [7:0] counter;
always @(posedge clock)
	counter <= counter + 1;
endmodule	

// test_simulation_always_23_test.v
module f9_MyCounter (clock, preset, updown, presetdata, counter);
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

// test_simulation_always_27_test.v
module f10_FlipFlop(clock, cs, ns);
input clock;
input cs;
output reg ns;
reg temp;

always @(posedge clock)
begin
    temp <= cs;
	ns <= temp;
end	

endmodule	

// test_simulation_always_29_test.v
module f11_test(input in, output reg [1:0] out);

    always @(in)
    begin
        out = in;
        out = out + in;
    end

endmodule
