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
    generate if (std_mode == "BYPASS") begin
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

    reg [MEM_WIDTH-1:0] mem [MEM_SIZE-1:0];

    integer i;
    initial begin
        for (i = 0; i < MEM_SIZE; i = i + 1)
            mem[i] = MEM_SIZE'b0;
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
            assign O[17:0] = mem[{ RA5, RA4, RA3, RA2, RA1 }];
        end
        else if (mode==1) begin
            assign O[17:0] = mem[{ WA5, WA4, WA3, WA2, WA1 }];
        end
        else if (mode==2) begin
            assign O[17:0] = mem[{ RA6, RA5, RA4, RA3, RA2, RA1 }];
        end
        else if (mode==3) begin
            assign O[35:0] = mem[{ RA5, RA4, RA3, RA2, RA1 }];
        end
        else if (mode==4) begin
            assign O[35:0] = { mem[{ RA10, RA9, RA8, RA7, RA6 }], mem[{ RA5, RA4, RA3, RA2, RA1 }] };
        end
        else 
            $error("Unknown NX_RFB_U mode");
    endgenerate

    always @(posedge clock)
        if (WE)
            mem[WA] <= I[MEM_WIDTH-1:0];
endmodule