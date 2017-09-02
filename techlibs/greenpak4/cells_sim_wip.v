
//Cells still in this file have INCOMPLETE simulation models, need to finish them

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

	initial RXD_HIGH = 0;
	initial RXD_LOW = 0;
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
