`timescale 1ns/1ps

/*
 This file contains analog / mixed signal cells, or other things that are not possible to fully model
 in behavioral Verilog.

 It also contains some stuff like oscillators that use non-synthesizeable constructs such as delays.
 TODO: do we want a third file for those cells?
 */

module GP_ABUF(input wire IN, output wire OUT);

	assign OUT = IN;

	//must be 1, 5, 20, 50
	//values >1 only available with Vdd > 2.7V
	parameter BANDWIDTH_KHZ = 1;

endmodule

module GP_ACMP(input wire PWREN, input wire VIN, input wire VREF, output reg OUT);

	parameter BANDWIDTH = "HIGH";
	parameter VIN_ATTEN = 1;
	parameter VIN_ISRC_EN = 0;
	parameter HYSTERESIS = 0;

	initial OUT = 0;

endmodule

module GP_BANDGAP(output reg OK);
	parameter AUTO_PWRDN = 1;
	parameter CHOPPER_EN = 1;
	parameter OUT_DELAY = 100;

endmodule

module GP_DAC(input[7:0] DIN, input wire VREF, output reg VOUT);

	initial VOUT = 0;

	//analog hard IP is not supported for simulation

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

module GP_PGA(input wire VIN_P, input wire VIN_N, input wire VIN_SEL, output reg VOUT);

	parameter GAIN = 1;
	parameter INPUT_MODE = "SINGLE";

	initial VOUT = 0;

	//cannot simulate mixed signal IP

endmodule

module GP_PWRDET(output reg VDD_LOW);
	initial VDD_LOW = 0;
endmodule

module GP_VREF(input VIN, output reg VOUT);
	parameter VIN_DIV = 1;
	parameter VREF = 0;
	//cannot simulate mixed signal IP
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
