`default_nettype none

// D flip-flop with async reset and enable
module \$_DFFE_PN0P_ (input D, C, R, E, output Q);
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(C), .ACLR(R), .ENA(E), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
endmodule

// D flip-flop with sync reset and enable (enable has priority)
module \$_SDFFCE_PP0P_ (input D, C, R, E, output Q);
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(C), .ACLR(1'b1), .ENA(E), .SCLR(R), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
endmodule
