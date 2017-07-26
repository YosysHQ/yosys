`default_nettype none
module top ( output wire [6:0] HEX0, HEX1, HEX2, HEX3, HEX4, HEX5, HEX6, HEX7,
             input  wire [15:0] SW );


    sevenseg UUD0 (.HEX0(HEX0), .SW(4'h7));
    sevenseg UUD1 (.HEX0(HEX1), .SW(4'h1));
    sevenseg UUD2 (.HEX0(HEX2), .SW(4'h0));
    sevenseg UUD3 (.HEX0(HEX3), .SW(4'h2));
    sevenseg UUD4 (.HEX0(HEX4), .SW(SW[3:0]));
    sevenseg UUD5 (.HEX0(HEX5), .SW(SW[7:4]));
    sevenseg UUD6 (.HEX0(HEX6), .SW(SW[11:8]));
    sevenseg UUD7 (.HEX0(HEX7), .SW(SW[15:12]));

endmodule
