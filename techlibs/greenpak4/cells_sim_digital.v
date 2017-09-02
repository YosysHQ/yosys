`timescale 1ns/1ps

/*
 This file contains simulation models for GreenPAK cells which are possible to fully model using synthesizeable
 behavioral Verilog constructs only.
 */

module GP_2LUT(input IN0, IN1, output OUT);
	parameter [3:0] INIT = 0;
	assign OUT = INIT[{IN1, IN0}];
endmodule

module GP_3LUT(input IN0, IN1, IN2, output OUT);
	parameter [7:0] INIT = 0;
	assign OUT = INIT[{IN2, IN1, IN0}];
endmodule

module GP_4LUT(
	input wire IN0,
	input wire IN1,
	input wire IN2,
	input wire IN3,
	output wire OUT);

	parameter [15:0] INIT = 0;
	assign OUT = INIT[{IN3, IN2, IN1, IN0}];
endmodule

module GP_CLKBUF(input wire IN, output wire OUT);
	assign OUT = IN;
endmodule

module GP_COUNT14(input CLK, input wire RST, output reg OUT);

	parameter RESET_MODE 	= "RISING";

	parameter COUNT_TO		= 14'h1;
	parameter CLKIN_DIVIDE	= 1;

	reg[13:0] count = COUNT_TO;

	initial begin
		if(CLKIN_DIVIDE != 1) begin
			$display("ERROR: CLKIN_DIVIDE values other than 1 not implemented");
			$finish;
		end
	end

	//Combinatorially output underflow flag whenever we wrap low
	always @(*) begin
		OUT <= (count == 14'h0);
	end

	//POR or SYSRST reset value is COUNT_TO. Datasheet is unclear but conversations w/ Silego confirm.
	//Runtime reset value is clearly 0 except in count/FSM cells where it's configurable but we leave at 0 for now.
	generate
		case(RESET_MODE)

			"RISING": begin
				always @(posedge CLK, posedge RST) begin
					if(RST)
						count		<= 0;
					else begin
						count		<= count - 1'd1;
						if(count == 0)
							count	<= COUNT_TO;
					end
				end
			end

			"FALLING": begin
				always @(posedge CLK, negedge RST) begin
					if(!RST)
						count		<= 0;
					else begin
						count		<= count - 1'd1;
						if(count == 0)
							count	<= COUNT_TO;
					end
				end
			end

			"BOTH": begin
				initial begin
					$display("Both-edge reset mode for GP_COUNT14 not implemented");
					$finish;
				end
			end

			"LEVEL": begin
				always @(posedge CLK, posedge RST) begin
					if(RST)
						count		<= 0;

					else begin
						count		<= count - 1'd1;
						if(count == 0)
							count	<= COUNT_TO;
					end
				end
			end

			default: begin
				initial begin
					$display("Invalid RESET_MODE on GP_COUNT14");
					$finish;
				end
			end

		endcase
	endgenerate

endmodule

module GP_COUNT14_ADV(input CLK, input RST, output reg OUT,
                     input UP, input KEEP, output reg[7:0] POUT);

	parameter RESET_MODE 	= "RISING";
	parameter RESET_VALUE   = "ZERO";

	parameter COUNT_TO		= 14'h1;
	parameter CLKIN_DIVIDE	= 1;

	initial begin
		if(CLKIN_DIVIDE != 1) begin
			$display("ERROR: CLKIN_DIVIDE values other than 1 not implemented");
			$finish;
		end
	end

	reg[13:0] count = COUNT_TO;

	//Combinatorially output underflow flag whenever we wrap low
	always @(*) begin
		if(UP)
			OUT <= (count == 14'h3fff);
		else
			OUT <= (count == 14'h0);
		POUT <= count[7:0];
	end

	//POR or SYSRST reset value is COUNT_TO. Datasheet is unclear but conversations w/ Silego confirm.
	//Runtime reset value is clearly 0 except in count/FSM cells where it's configurable but we leave at 0 for now.
	generate
		case(RESET_MODE)

			"RISING": begin
				always @(posedge CLK, posedge RST) begin

					//Resets
					if(RST) begin
						if(RESET_VALUE == "ZERO")
							count	<= 0;
						else
							count	<= COUNT_TO;
					end

					else if(KEEP) begin
					end
					else if(UP) begin
						count		<= count + 1'd1;
						if(count == 14'h3fff)
							count	<= COUNT_TO;
					end
					else begin
						count		<= count - 1'd1;

						if(count == 0)
							count	<= COUNT_TO;
					end

				end
			end

			"FALLING": begin
				always @(posedge CLK, negedge RST) begin

					//Resets
					if(!RST) begin
						if(RESET_VALUE == "ZERO")
							count	<= 0;
						else
							count	<= COUNT_TO;
					end

					else if(KEEP) begin
					end
					else if(UP) begin
						count		<= count + 1'd1;
						if(count == 14'h3fff)
							count	<= COUNT_TO;
					end
					else begin
						count		<= count - 1'd1;

						if(count == 0)
							count	<= COUNT_TO;
					end

				end
			end

			"BOTH": begin
				initial begin
					$display("Both-edge reset mode for GP_COUNT14_ADV not implemented");
					$finish;
				end
			end

			"LEVEL": begin
				always @(posedge CLK, posedge RST) begin

					//Resets
					if(RST) begin
						if(RESET_VALUE == "ZERO")
							count	<= 0;
						else
							count	<= COUNT_TO;
					end

					else begin

						if(KEEP) begin
						end
						else if(UP) begin
							count		<= count + 1'd1;
							if(count == 14'h3fff)
								count	<= COUNT_TO;
						end
						else begin
							count		<= count - 1'd1;

							if(count == 0)
								count	<= COUNT_TO;
						end

					end

				end
			end

			default: begin
				initial begin
					$display("Invalid RESET_MODE on GP_COUNT14_ADV");
					$finish;
				end
			end

		endcase
	endgenerate

endmodule

module GP_COUNT8_ADV(input CLK, input RST, output reg OUT,
                     input UP, input KEEP, output reg[7:0] POUT);

	parameter RESET_MODE 	= "RISING";
	parameter RESET_VALUE   = "ZERO";

	parameter COUNT_TO		= 8'h1;
	parameter CLKIN_DIVIDE	= 1;

	reg[7:0] count = COUNT_TO;

	initial begin
		if(CLKIN_DIVIDE != 1) begin
			$display("ERROR: CLKIN_DIVIDE values other than 1 not implemented");
			$finish;
		end
	end

	//Combinatorially output underflow flag whenever we wrap low
	always @(*) begin
		if(UP)
			OUT <= (count == 8'hff);
		else
			OUT <= (count == 8'h0);
		POUT <= count;
	end

	//POR or SYSRST reset value is COUNT_TO. Datasheet is unclear but conversations w/ Silego confirm.
	//Runtime reset value is clearly 0 except in count/FSM cells where it's configurable but we leave at 0 for now.
	generate
		case(RESET_MODE)

			"RISING": begin
				always @(posedge CLK, posedge RST) begin

					//Resets
					if(RST) begin
						if(RESET_VALUE == "ZERO")
							count	<= 0;
						else
							count	<= COUNT_TO;
					end

					//Main counter
					else if(KEEP) begin
					end
					else if(UP) begin
						count		<= count + 1'd1;
						if(count == 8'hff)
							count	<= COUNT_TO;
					end
					else begin
						count		<= count - 1'd1;

						if(count == 0)
							count	<= COUNT_TO;
					end

				end
			end

			"FALLING": begin
				always @(posedge CLK, negedge RST) begin

					//Resets
					if(!RST) begin
						if(RESET_VALUE == "ZERO")
							count	<= 0;
						else
							count	<= COUNT_TO;
					end

					//Main counter
					else if(KEEP) begin
					end
					else if(UP) begin
						count		<= count + 1'd1;
						if(count == 8'hff)
							count	<= COUNT_TO;
					end
					else begin
						count		<= count - 1'd1;

						if(count == 0)
							count	<= COUNT_TO;
					end

				end
			end

			"BOTH": begin
				initial begin
					$display("Both-edge reset mode for GP_COUNT8_ADV not implemented");
					$finish;
				end
			end

			"LEVEL": begin
				always @(posedge CLK, posedge RST) begin

					//Resets
					if(RST) begin
						if(RESET_VALUE == "ZERO")
							count	<= 0;
						else
							count	<= COUNT_TO;
					end

					else begin

						if(KEEP) begin
						end
						else if(UP) begin
							count		<= count + 1'd1;
							if(count == 8'hff)
								count	<= COUNT_TO;
						end
						else begin
							count		<= count - 1'd1;

							if(count == 0)
								count	<= COUNT_TO;
						end
					end

				end
			end

			default: begin
				initial begin
					$display("Invalid RESET_MODE on GP_COUNT8_ADV");
					$finish;
				end
			end

		endcase
	endgenerate

endmodule

module GP_COUNT8(
	input wire CLK,
	input wire RST,
	output reg OUT,
	output reg[7:0] POUT);

	parameter RESET_MODE 	= "RISING";

	parameter COUNT_TO		= 8'h1;
	parameter CLKIN_DIVIDE	= 1;

	initial begin
		if(CLKIN_DIVIDE != 1) begin
			$display("ERROR: CLKIN_DIVIDE values other than 1 not implemented");
			$finish;
		end
	end

	reg[7:0] count = COUNT_TO;

	//Combinatorially output underflow flag whenever we wrap low
	always @(*) begin
		OUT <= (count == 8'h0);
		POUT <= count;
	end

	//POR or SYSRST reset value is COUNT_TO. Datasheet is unclear but conversations w/ Silego confirm.
	//Runtime reset value is clearly 0 except in count/FSM cells where it's configurable but we leave at 0 for now.
	generate
		case(RESET_MODE)

			"RISING": begin
				always @(posedge CLK, posedge RST) begin
					if(RST)
						count	<= 0;
					else begin
						count		<= count - 1'd1;
						if(count == 0)
							count	<= COUNT_TO;
					end
				end
			end

			"FALLING": begin
				always @(posedge CLK, negedge RST) begin
					if(!RST)
						count	<= 0;
					else begin
						count		<= count - 1'd1;
						if(count == 0)
							count	<= COUNT_TO;
					end
				end
			end

			"BOTH": begin
				initial begin
					$display("Both-edge reset mode for GP_COUNT8 not implemented");
					$finish;
				end
			end

			"LEVEL": begin
				always @(posedge CLK, posedge RST) begin
					if(RST)
						count	<= 0;

					else begin
						count		<= count - 1'd1;
						if(count == 0)
							count	<= COUNT_TO;
					end
				end
			end

			default: begin
				initial begin
					$display("Invalid RESET_MODE on GP_COUNT8");
					$finish;
				end
			end

		endcase
	endgenerate

endmodule

module GP_DCMPREF(output reg[7:0]OUT);
	parameter[7:0] REF_VAL = 8'h00;
	initial OUT = REF_VAL;
endmodule

module GP_DCMPMUX(input[1:0] SEL, input[7:0] IN0, input[7:0] IN1, input[7:0] IN2, input[7:0] IN3, output reg[7:0] OUTA, output reg[7:0] OUTB);

	always @(*) begin
		case(SEL)
			2'd00: begin
				OUTA <= IN0;
				OUTB <= IN3;
			end

			2'd01: begin
				OUTA <= IN1;
				OUTB <= IN2;
			end

			2'd02: begin
				OUTA <= IN2;
				OUTB <= IN1;
			end

			2'd03: begin
				OUTA <= IN3;
				OUTB <= IN0;
			end

		endcase
	end
endmodule

module GP_DELAY(input IN, output reg OUT);

	parameter DELAY_STEPS = 1;
	parameter GLITCH_FILTER = 0;

	initial OUT = 0;

	generate

		if(GLITCH_FILTER) begin
			initial begin
				$display("ERROR: GP_DELAY glitch filter mode not implemented");
				$finish;
			end
		end

		//TODO: These delays are PTV dependent! For now, hard code 3v3 timing
		//Change simulation-mode delay depending on global Vdd range (how to specify this?)
		always @(*) begin
			case(DELAY_STEPS)
				1: #166 OUT = IN;
				2: #318 OUT = IN;
				2: #471 OUT = IN;
				3: #622 OUT = IN;
				default: begin
					$display("ERROR: GP_DELAY must have DELAY_STEPS in range [1,4]");
					$finish;
				end
			endcase
		end

	endgenerate

endmodule

module GP_DFF(input D, CLK, output reg Q);
	parameter [0:0] INIT = 1'bx;
	initial Q = INIT;
	always @(posedge CLK) begin
		Q <= D;
	end
endmodule

module GP_DFFI(input D, CLK, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	initial nQ = INIT;
	always @(posedge CLK) begin
		nQ <= ~D;
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

module GP_DFFRI(input D, CLK, nRST, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	initial nQ = INIT;
	always @(posedge CLK, negedge nRST) begin
		if (!nRST)
			nQ <= 1'b1;
		else
			nQ <= ~D;
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

module GP_DFFSI(input D, CLK, nSET, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	initial nQ = INIT;
	always @(posedge CLK, negedge nSET) begin
		if (!nSET)
			nQ <= 1'b0;
		else
			nQ <= ~D;
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

module GP_DFFSRI(input D, CLK, nSR, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	parameter [0:0] SRMODE = 1'bx;
	initial nQ = INIT;
	always @(posedge CLK, negedge nSR) begin
		if (!nSR)
			nQ <= ~SRMODE;
		else
			nQ <= ~D;
	end
endmodule

module GP_DLATCH(input D, input nCLK, output reg Q);
	parameter [0:0] INIT = 1'bx;
	initial Q = INIT;
	always @(*) begin
		if(!nCLK)
			Q <= D;
	end
endmodule

module GP_DLATCHI(input D, input nCLK, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	initial nQ = INIT;
	always @(*) begin
		if(!nCLK)
			nQ <= ~D;
	end
endmodule

module GP_DLATCHR(input D, input nCLK, input nRST, output reg Q);
	parameter [0:0] INIT = 1'bx;
	initial Q = INIT;
	always @(*) begin
		if(!nRST)
			Q <= 1'b0;
		else if(!nCLK)
			Q <= D;
	end
endmodule

module GP_DLATCHRI(input D, input nCLK, input nRST, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	initial nQ = INIT;
	always @(*) begin
		if(!nRST)
			nQ <= 1'b1;
		else if(!nCLK)
			nQ <= ~D;
	end
endmodule

module GP_DLATCHS(input D, input nCLK, input nSET, output reg Q);
	parameter [0:0] INIT = 1'bx;
	initial Q = INIT;
	always @(*) begin
		if(!nSET)
			Q <= 1'b1;
		else if(!nCLK)
			Q <= D;
	end
endmodule

module GP_DLATCHSI(input D, input nCLK, input nSET, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	initial nQ = INIT;
	always @(*) begin
		if(!nSET)
			nQ <= 1'b0;
		else if(!nCLK)
			nQ <= ~D;
	end
endmodule

module GP_DLATCHSR(input D, input nCLK, input nSR, output reg Q);
	parameter [0:0] INIT = 1'bx;
	parameter[0:0] SRMODE = 1'bx;
	initial Q = INIT;
	always @(*) begin
		if(!nSR)
			Q <= SRMODE;
		else if(!nCLK)
			Q <= D;
	end
endmodule

module GP_DLATCHSRI(input D, input nCLK, input nSR, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	parameter[0:0] SRMODE = 1'bx;
	initial nQ = INIT;
	always @(*) begin
		if(!nSR)
			nQ <= ~SRMODE;
		else if(!nCLK)
			nQ <= ~D;
	end
endmodule

module GP_IBUF(input IN, output OUT);
	assign OUT = IN;
endmodule

module GP_IOBUF(input IN, input OE, output OUT, inout IO);
	assign OUT = IO;
	assign IO = OE ? IN : 1'bz;
endmodule

module GP_INV(input IN, output OUT);
	assign OUT = ~IN;
endmodule

module GP_OBUF(input IN, output OUT);
	assign OUT = IN;
endmodule

module GP_OBUFT(input IN, input OE, output OUT);
	assign OUT = OE ? IN : 1'bz;
endmodule

module GP_PGEN(input wire nRST, input wire CLK, output reg OUT);
	initial OUT = 0;
	parameter PATTERN_DATA = 16'h0;
	parameter PATTERN_LEN = 5'd16;

	localparam COUNT_MAX =  PATTERN_LEN - 1'h1;

	reg[3:0] count = 0;
	always @(posedge CLK, negedge nRST) begin

		if(!nRST)
			count	<= 0;

		else begin
			count	<= count - 1'h1;
			if(count == 0)
				count <= COUNT_MAX;
		end
	end

	always @(*)
		OUT	= PATTERN_DATA[count];

endmodule

module GP_SHREG(input nRST, input CLK, input IN, output OUTA, output OUTB);

	parameter OUTA_TAP = 1;
	parameter OUTA_INVERT = 0;
	parameter OUTB_TAP = 1;

	reg[15:0] shreg = 0;

	always @(posedge CLK, negedge nRST) begin

		if(!nRST)
			shreg = 0;

		else
			shreg <= {shreg[14:0], IN};

	end

	assign OUTA = (OUTA_INVERT) ? ~shreg[OUTA_TAP - 1] : shreg[OUTA_TAP - 1];
	assign OUTB = shreg[OUTB_TAP - 1];

endmodule

module GP_VDD(output OUT);
       assign OUT = 1;
endmodule

module GP_VSS(output OUT);
       assign OUT = 0;
endmodule
