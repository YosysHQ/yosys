(* abc9_box, lib_whitebox *)
module NX_GCK_U(SI1, SI2, CMD, SO);
    input CMD;
    input SI1;
    input SI2;
    output SO;
    parameter inv_in = 1'b0;
    parameter inv_out = 1'b0;
    parameter std_mode = "BYPASS";

    wire SI1_int = inv_in ? ~SI1 : SI1;
    wire SI2_int = inv_in ? ~SI2 : SI2;

    wire SO_int;
    generate
        if (std_mode == "BYPASS") begin
            assign SO_int = SI1_int;
        end
        else if (std_mode == "MUX") begin
            assign SO_int = CMD ? SI1_int : SI2_int;
        end
        else if (std_mode == "CKS") begin
            assign SO_int = CMD ? SI1_int : 1'b0;
        end
        else if (std_mode == "CSC") begin
            assign SO_int = CMD;
        end
        else
            $error("Unrecognised std_mode");
    endgenerate
    assign SO = inv_out ? ~SO_int : SO_int;
endmodule

(* abc9_box, lib_whitebox *)
module NX_RFB_U(WCK, I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15, I16, I17, I18, I19, I20
, I21, I22, I23, I24, I25, I26, I27, I28, I29, I30, I31, I32, I33, I34, I35, I36, O1, O2, O3, O4, O5
, O6, O7, O8, O9, O10, O11, O12, O13, O14, O15, O16, O17, O18, O19, O20, O21, O22, O23, O24, O25, O26
, O27, O28, O29, O30, O31, O32, O33, O34, O35, O36, RA1, RA2, RA3, RA4, RA5, RA6, RA7, RA8, RA9, RA10, WA1
, WA2, WA3, WA4, WA5, WA6, WE, WEA);
    input I1;
    input I10;
    input I11;
    input I12;
    input I13;
    input I14;
    input I15;
    input I16;
    input I17;
    input I18;
    input I19;
    input I2;
    input I20;
    input I21;
    input I22;
    input I23;
    input I24;
    input I25;
    input I26;
    input I27;
    input I28;
    input I29;
    input I3;
    input I30;
    input I31;
    input I32;
    input I33;
    input I34;
    input I35;
    input I36;
    input I4;
    input I5;
    input I6;
    input I7;
    input I8;
    input I9;
    output O1;
    output O10;
    output O11;
    output O12;
    output O13;
    output O14;
    output O15;
    output O16;
    output O17;
    output O18;
    output O19;
    output O2;
    output O20;
    output O21;
    output O22;
    output O23;
    output O24;
    output O25;
    output O26;
    output O27;
    output O28;
    output O29;
    output O3;
    output O30;
    output O31;
    output O32;
    output O33;
    output O34;
    output O35;
    output O36;
    output O4;
    output O5;
    output O6;
    output O7;
    output O8;
    output O9;
    input RA1;
    input RA10;
    input RA2;
    input RA3;
    input RA4;
    input RA5;
    input RA6;
    input RA7;
    input RA8;
    input RA9;
    input WA1;
    input WA2;
    input WA3;
    input WA4;
    input WA5;
    input WA6;
    input WCK;
    input WE;
    input WEA;
    parameter mem_ctxt = "";
    parameter mode = 0;
    parameter wck_edge = 1'b0;

    wire clock = WCK ^ wck_edge;

    localparam MEM_SIZE  = mode == 2 ? 64 : 32;
    localparam MEM_WIDTH = mode == 3 ? 36 : 18;
    localparam ADDR_WIDTH = mode == 2 ? 6 : 5;
    localparam DATA_SIZE = MEM_SIZE * MEM_WIDTH;
    localparam MAX_SIZE = DATA_SIZE + MEM_SIZE + 1;

    reg [MEM_WIDTH-1:0] mem [MEM_SIZE-1:0];

	function [DATA_SIZE-1:0] convert_initval;
		input [8*MAX_SIZE-1:0] hex_initval;
		reg done;
		reg [DATA_SIZE-1:0] temp;
		reg [7:0] char;
		integer i,j;
		begin
			done = 1'b0;
			temp = 0;
            j = 0;
			for (i = 0; i < MAX_SIZE; i = i + 1) begin
                char = hex_initval[8*i +: 8];
                if (char >= "0" && char <= "1") begin
                    temp[j] = char - "0";
                    j = j + 1;
                end
			end
			convert_initval = temp;
		end
	endfunction

    integer i;
    reg [DATA_SIZE-1:0] mem_data;
    initial begin
        mem_data = convert_initval(mem_ctxt);
        for (i = 0; i < MEM_SIZE; i = i + 1)
            mem[i] = mem_data[MEM_WIDTH*(MEM_SIZE-i-1) +: MEM_WIDTH];
    end

    wire [ADDR_WIDTH-1:0] WA = (mode==2) ? { WA6, WA5, WA4, WA3, WA2, WA1 } : { WA5, WA4, WA3, WA2, WA1 };
    wire [36-1:0] O = { O36, O35, O34, O33, O32, O31, O30, O29, O28, 
                        O27, O26, O25, O24, O23, O22, O21, O20, O19, 
                        O18, O17, O16, O15, O14, O13, O12, O11, O10,
                         O9,  O8,  O7,  O6,  O5,  O4,  O3,  O2,  O1 };
    wire [36-1:0] I = { I36, I35, I34, I33, I32, I31, I30, I29, I28,
                        I27, I26, I25, I24, I23, I22, I21, I20, I19,
                        I18, I17, I16, I15, I14, I13, I12, I11, I10,
                         I9,  I8,  I7,  I6,  I5,  I4,  I3,  I2,  I1 };
    generate 
        if (mode==0) begin
            assign O = mem[{ RA5, RA4, RA3, RA2, RA1 }];
        end
        else if (mode==1) begin
            assign O = mem[{ WA5, WA4, WA3, WA2, WA1 }];
        end
        else if (mode==2) begin
            assign O = mem[{ RA6, RA5, RA4, RA3, RA2, RA1 }];
        end
        else if (mode==3) begin
            assign O = mem[{ RA5, RA4, RA3, RA2, RA1 }];
        end
        else if (mode==4) begin
            assign O = { mem[{ RA10, RA9, RA8, RA7, RA6 }], mem[{ RA5, RA4, RA3, RA2, RA1 }] };
        end
        else 
            $error("Unknown NX_RFB_U mode");
    endgenerate

    always @(posedge clock)
        if (WE)
            mem[WA] <= I[MEM_WIDTH-1:0];
endmodule

(* abc9_box, lib_whitebox *)
module NX_WFG_U(R, SI, ZI, SO, ZO);
    input R;
    input SI;
    output SO;
    input ZI;
    output ZO;
    parameter delay = 0;
    parameter delay_on = 1'b0;
    parameter div_phase = 1'b0;
    parameter div_ratio = 0;
    parameter location = "";
    parameter mode = 0;
    parameter pattern = 16'b0000000000000000;
    parameter pattern_end = 0;
    parameter reset_on_cal_lock_n = 1'b0;
    parameter reset_on_pll_lock_n = 1'b0;
    parameter reset_on_pll_locka_n = 1'b0;
    parameter wfg_edge = 1'b0;

    generate
        if (mode==0) begin
            assign SO = SI;
        end
        else if (mode==1) begin
            wire clock = ZI ^ wfg_edge;
            wire reset = R || SI;
            reg [3:0] counter = 0;
            reg [15:0] rom = pattern;

            always @(posedge clock)
            begin
                if (reset)
                    counter <= 4'b0;
                else
                    counter <= counter + 1;
            end
            assign SO = counter == pattern_end;
            assign ZO = rom[counter];
        end
        else if (mode==2) begin
        end
        else
            $error("Unknown NX_WFG_U mode");
    endgenerate
endmodule

module NX_DDFR_U(CK,CKF,R,I,I2,L,O,O2);
    input CK;
    input CKF;
    input R;
    input I;
    input I2;
    input L;
    output O;
    output O2;

    parameter location = "";
    parameter path = 0;
    parameter dff_type = 1'b0;
    parameter dff_sync = 1'b0;
    parameter dff_load = 1'b0;

    wire load = dff_load ? 1'b1 : L; // reversed when compared to DFF
    wire async_reset = !dff_sync && R;
    wire sync_reset = dff_sync && R;

    generate
        if (path==1) begin
            // IDDFR
            always @(posedge CK, posedge async_reset)
                if (async_reset) O <= dff_type;
                else if (sync_reset) O <= dff_type;
                else if (load) O <= I;

            always @(posedge CKF, posedge async_reset)
                if (async_reset) O2 <= dff_type;
                else if (sync_reset) O2 <= dff_type;
                else if (load) O2 <= I;
        end
        else if (path==0 || path==2) begin
            reg q1, q2;
            // ODDFR
            always @(posedge CK, posedge async_reset)
                if (async_reset) q1 <= dff_type;
                else if (sync_reset) q1 <= dff_type;
                else if (load) q1 <= I;

            always @(posedge CKF, posedge async_reset)
                if (async_reset) q2 <= dff_type;
                else if (sync_reset) q2 <= dff_type;
                else if (load) q2 <= I2;

            assign O = CK ? q1 : q2;
        end
        else
            $error("Unknown NX_DDFR_U path");
    endgenerate
endmodule
