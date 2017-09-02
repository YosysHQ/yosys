module \$__COUNT_ (CE, CLK, OUT, POUT, RST, UP);

	input wire CE;
	input wire CLK;
	output reg OUT;
	output reg[WIDTH-1:0] POUT;
	input wire RST;
	input wire UP;

	parameter COUNT_TO = 1;
	parameter RESET_MODE = "RISING";
	parameter HAS_POUT = 0;
	parameter HAS_CE = 0;
	parameter WIDTH = 8;
	parameter DIRECTION = "DOWN";

endmodule
