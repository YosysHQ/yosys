`timescale 1ns/1ps

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

module GP_ABUF(input wire IN, output wire OUT);

	assign OUT = IN;

	//must be 1, 5, 20, 50
	//values >1 only available with Vdd > 2.7V
	parameter BANDWIDTH_KHZ = 1;

	//cannot simulate mixed signal IP

endmodule

module GP_ACMP(input wire PWREN, input wire VIN, input wire VREF, output reg OUT);

	parameter BANDWIDTH = "HIGH";
	parameter VIN_ATTEN = 1;
	parameter VIN_ISRC_EN = 0;
	parameter HYSTERESIS = 0;

	initial OUT = 0;

	//cannot simulate mixed signal IP

endmodule

module GP_BANDGAP(output reg OK);
	parameter AUTO_PWRDN = 1;
	parameter CHOPPER_EN = 1;
	parameter OUT_DELAY = 100;

	//cannot simulate mixed signal IP

endmodule

module GP_CLKBUF(input wire IN, output wire OUT);
	assign OUT = IN;
endmodule

module GP_COUNT8(input CLK, input wire RST, output reg OUT, output reg[7:0] POUT);

	parameter RESET_MODE 	= "RISING";

	parameter COUNT_TO		= 8'h1;
	parameter CLKIN_DIVIDE	= 1;

	//more complex hard IP blocks are not supported for simulation yet

	reg[7:0] count = COUNT_TO;

	//Combinatorially output whenever we wrap low
	always @(*) begin
		OUT <= (count == 8'h0);
		OUT <= count;
	end

	//POR or SYSRST reset value is COUNT_TO. Datasheet is unclear but conversations w/ Silego confirm.
	//Runtime reset value is clearly 0 except in count/FSM cells where it's configurable but we leave at 0 for now.
	//Datasheet seems to indicate that reset is asynchronous, but for now we model as sync due to Yosys issues...
	always @(posedge CLK) begin

		count		<= count - 1'd1;

		if(count == 0)
			count	<= COUNT_TO;

		/*
		if((RESET_MODE == "RISING") && RST)
			count	<= 0;
		if((RESET_MODE == "FALLING") && !RST)
			count	<= 0;
		if((RESET_MODE == "BOTH") && RST)
			count	<= 0;
		*/
	end

endmodule

module GP_COUNT14(input CLK, input wire RST, output reg OUT);

	parameter RESET_MODE 	= "RISING";

	parameter COUNT_TO		= 14'h1;
	parameter CLKIN_DIVIDE	= 1;

	//more complex hard IP blocks are not supported for simulation yet

endmodule

module GP_COUNT8_ADV(input CLK, input RST, output reg OUT,
                     input UP, input KEEP, output reg[7:0] POUT);

	parameter RESET_MODE 	= "RISING";
	parameter RESET_VALUE   = "ZERO";

	parameter COUNT_TO		= 8'h1;
	parameter CLKIN_DIVIDE	= 1;

	//more complex hard IP blocks are not supported for simulation yet

endmodule

module GP_COUNT14_ADV(input CLK, input RST, output reg OUT,
                      input UP, input KEEP, output reg[7:0] POUT);

	parameter RESET_MODE 	= "RISING";
	parameter RESET_VALUE   = "ZERO";

	parameter COUNT_TO		= 14'h1;
	parameter CLKIN_DIVIDE	= 1;

	//more complex hard IP blocks are not supported for simulation yet

endmodule

module GP_DAC(input[7:0] DIN, input wire VREF, output reg VOUT);

	initial VOUT = 0;

	//analog hard IP is not supported for simulation

endmodule

module GP_DCMP(input[7:0] INP, input[7:0] INN, input CLK, input PWRDN, output reg GREATER, output reg EQUAL);
	parameter PWRDN_SYNC = 1'b0;
	parameter CLK_EDGE = "RISING";
	parameter GREATER_OR_EQUAL = 1'b0;

	//TODO implement power-down mode

	initial GREATER = 0;
	initial EQUAL = 0;

	wire clk_minv = (CLK_EDGE == "RISING") ? CLK : ~CLK;
	always @(posedge clk_minv) begin
		if(GREATER_OR_EQUAL)
			GREATER <= (INP >= INN);
		else
			GREATER <= (INP > INN);

		EQUAL <= (INP == INN);
	end

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

module GP_EDGEDET(input IN, output reg OUT);

	parameter EDGE_DIRECTION = "RISING";
	parameter DELAY_STEPS = 1;
	parameter GLITCH_FILTER = 0;

	//not implemented for simulation

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

module GP_LFOSC(input PWRDN, output reg CLKOUT);

	parameter PWRDN_EN = 0;
	parameter AUTO_PWRDN = 0;
	parameter OUT_DIV = 1;

	initial CLKOUT = 0;

	//auto powerdown not implemented for simulation
	//output dividers not implemented for simulation

	always begin
		if(PWRDN)
			CLKOUT = 0;
		else begin
			//half period of 1730 Hz
			#289017;
			CLKOUT = ~CLKOUT;
		end
	end

endmodule

module GP_OBUF(input IN, output OUT);
	assign OUT = IN;
endmodule

module GP_OBUFT(input IN, input OE, output OUT);
	assign OUT = OE ? IN : 1'bz;
endmodule

module GP_PGA(input wire VIN_P, input wire VIN_N, input wire VIN_SEL, output reg VOUT);

	parameter GAIN = 1;
	parameter INPUT_MODE = "SINGLE";

	initial VOUT = 0;

	//cannot simulate mixed signal IP

endmodule

module GP_PGEN(input wire nRST, input wire CLK, output reg OUT);
	initial OUT = 0;
	parameter PATTERN_DATA = 16'h0;
	parameter PATTERN_LEN = 5'd16;

	reg[3:0] count = 0;
	always @(posedge CLK) begin
		if(!nRST)
			OUT <= PATTERN_DATA[0];

		else begin
			count <= count + 1;
			OUT <= PATTERN_DATA[count];

			if( (count + 1) == PATTERN_LEN)
				count <= 0;
		end
	end

endmodule

module GP_PWRDET(output reg VDD_LOW);
	initial VDD_LOW = 0;
endmodule

module GP_POR(output reg RST_DONE);
	parameter POR_TIME = 500;

	initial begin
		RST_DONE = 0;

		if(POR_TIME == 4)
			#4000;
		else if(POR_TIME == 500)
			#500000;
		else begin
			$display("ERROR: bad POR_TIME for GP_POR cell");
			$finish;
		end

		RST_DONE = 1;

	end

endmodule

module GP_RCOSC(input PWRDN, output reg CLKOUT_HARDIP, output reg CLKOUT_FABRIC);

	parameter PWRDN_EN = 0;
	parameter AUTO_PWRDN = 0;
	parameter HARDIP_DIV = 1;
	parameter FABRIC_DIV = 1;
	parameter OSC_FREQ = "25k";

	initial CLKOUT_HARDIP = 0;
	initial CLKOUT_FABRIC = 0;

	//output dividers not implemented for simulation
	//auto powerdown not implemented for simulation

	always begin
		if(PWRDN) begin
			CLKOUT_HARDIP = 0;
			CLKOUT_FABRIC = 0;
		end
		else begin

			if(OSC_FREQ == "25k") begin
				//half period of 25 kHz
				#20000;
			end

			else begin
				//half period of 2 MHz
				#250;
			end

			CLKOUT_HARDIP = ~CLKOUT_HARDIP;
			CLKOUT_FABRIC = ~CLKOUT_FABRIC;
		end
	end

endmodule

module GP_RINGOSC(input PWRDN, output reg CLKOUT_HARDIP, output reg CLKOUT_FABRIC);

	parameter PWRDN_EN = 0;
	parameter AUTO_PWRDN = 0;
	parameter HARDIP_DIV = 1;
	parameter FABRIC_DIV = 1;

	initial CLKOUT_HARDIP = 0;
	initial CLKOUT_FABRIC = 0;

	//output dividers not implemented for simulation
	//auto powerdown not implemented for simulation

	always begin
		if(PWRDN) begin
			CLKOUT_HARDIP = 0;
			CLKOUT_FABRIC = 0;
		end
		else begin
			//half period of 27 MHz
			#18.518;
			CLKOUT_HARDIP = ~CLKOUT_HARDIP;
			CLKOUT_FABRIC = ~CLKOUT_FABRIC;
		end
	end

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

module GP_SPI(
	input SCK,
	inout SDAT,
	input CSN,
	input[7:0] TXD_HIGH,
	input[7:0] TXD_LOW,
	output reg[7:0] RXD_HIGH,
	output reg[7:0] RXD_LOW,
	output reg INT);

	initial DOUT_HIGH = 0;
	initial DOUT_LOW = 0;
	initial INT = 0;

	parameter DATA_WIDTH = 8;		//byte or word width
	parameter SPI_CPHA = 0;			//SPI clock phase
	parameter SPI_CPOL = 0;			//SPI clock polarity
	parameter DIRECTION = "INPUT";	//SPI data direction (either input to chip or output to host)
	//parallel output to fabric not yet implemented

	//TODO: write sim model
	//TODO: SPI SDIO control... can we use ADC output while SPI is input??
	//TODO: clock sync

endmodule

//keep constraint needed to prevent optimization since we have no outputs
(* keep *)
module GP_SYSRESET(input RST);
	parameter RESET_MODE = "EDGE";
	parameter EDGE_SPEED = 4;

	//cannot simulate whole system reset

endmodule

module GP_VDD(output OUT);
       assign OUT = 1;
endmodule

module GP_VREF(input VIN, output reg VOUT);
	parameter VIN_DIV = 1;
	parameter VREF = 0;
	//cannot simulate mixed signal IP
endmodule

module GP_VSS(output OUT);
       assign OUT = 0;
endmodule
