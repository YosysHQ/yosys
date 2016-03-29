module GP_DFF(input D, CLK, output reg Q);
	parameter [0:0] INIT = 1'bx;
	initial Q = INIT;
	always @(posedge CLK) begin
		Q <= D;
	end
endmodule

module GP_DFFS(input D, CLK, nSET, output reg Q);
	parameter [0:0] INIT = 1'bx;
	initial Q = INIT;
	always @(posedge CLK, negedge nSET) begin
		if (!nSET)
			Q <= 1'b1;
		else
			Q <= D;
	end
endmodule

module GP_DFFR(input D, CLK, nRST, output reg Q);
	parameter [0:0] INIT = 1'bx;
	initial Q = INIT;
	always @(posedge CLK, negedge nRST) begin
		if (!nRST)
			Q <= 1'b0;
		else
			Q <= D;
	end
endmodule

module GP_DFFSR(input D, CLK, nSR, output reg Q);
	parameter [0:0] INIT = 1'bx;
	parameter [0:0] SRMODE = 1'bx;
	initial Q = INIT;
	always @(posedge CLK, negedge nSR) begin
		if (!nSR)
			Q <= SRMODE;
		else
			Q <= D;
	end
endmodule

module GP_2LUT(input IN0, IN1, output OUT);
	parameter [3:0] INIT = 0;
	assign OUT = INIT[{IN1, IN0}];
endmodule

module GP_3LUT(input IN0, IN1, IN2, output OUT);
	parameter [7:0] INIT = 0;
	assign OUT = INIT[{IN2, IN1, IN0}];
endmodule

module GP_4LUT(input IN0, IN1, IN2, IN3, output OUT);
	parameter [15:0] INIT = 0;
	assign OUT = INIT[{IN3, IN2, IN1, IN0}];
endmodule

module GP_VDD(output OUT);
       assign OUT = 1;
endmodule

module GP_VSS(output OUT);
       assign OUT = 0;
endmodule

module GP_LFOSC(input PWRDN, output reg CLKOUT);
	
	parameter PWRDN_EN = 0;
	parameter AUTO_PWRDN = 0;
	parameter OUT_DIV = 1;
	
	initial CLKOUT = 0;
	
	always begin
		if(PWRDN)
			clkout = 0;
		else begin
			//half period of 1730 Hz
			#289017;
			clkout = ~clkout;
		end
	end
	
endmodule

module GP_COUNT8(input CLK, input wire RST, output reg OUT);

	parameter RESET_MODE 	= "RISING";	
	
	parameter COUNT_TO		= 8'h1;
	parameter CLKIN_DIVIDE	= 1;
	
	//more complex hard IP blocks are not supported for simulation yet

endmodule

module GP_COUNT14(input CLK, input wire RST, output reg OUT);

	parameter RESET_MODE 	= "RISING";	
	
	parameter COUNT_TO		= 14'h1;
	parameter CLKIN_DIVIDE	= 1;
	
	//more complex hard IP blocks are not supported for simulation yet

endmodule

module GP_SYSRESET(input RST);
	parameter RESET_MODE = "RISING";
	
	//cannot simulate whole system reset
	
endmodule
