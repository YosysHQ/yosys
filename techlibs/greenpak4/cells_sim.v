`timescale 1ns/1ps

`include "cells_sim_ams.v"
`include "cells_sim_digital.v"

//Cells still in this file have INCOMPLETE simulation models, need to finish them

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

module GP_EDGEDET(input IN, output reg OUT);

	parameter EDGE_DIRECTION = "RISING";
	parameter DELAY_STEPS = 1;
	parameter GLITCH_FILTER = 0;

	//not implemented for simulation

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
