`default_nettype none

// D flip-flops
module \$_DFF_P_ (input D, C, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(C), .ACLR(1'b1), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop that initialises to one");
endmodule

module \$_DFF_N_ (input D, C, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(~C), .ACLR(1'b1), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop that initialises to one");
endmodule

// D flip-flops with reset
module \$_DFF_PP0_ (input D, C, R, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(C), .ACLR(~R), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop with reset that initialises to one");
endmodule

module \$_DFF_PN0_ (input D, C, R, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(C), .ACLR(R), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop with reset that initialises to one");
endmodule

module \$_DFF_NP0_ (input D, C, R, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(~C), .ACLR(~R), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop with reset that initialises to one");
endmodule

module \$_DFF_NN0_ (input D, C, R, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(~C), .ACLR(R), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop with reset that initialises to one");
endmodule

// D flip-flops with set
module \$_DFF_PP1_ (input D, C, R, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b1;
if (_TECHMAP_WIREINIT_Q_ !== 1'b0) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    wire Q_tmp;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(~D), .CLK(C), .ACLR(~R), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q_tmp));
    assign Q = ~Q_tmp;
end else $error("Cannot implement a flip-flop with set that initialises to zero");
endmodule

module \$_DFF_PN1_ (input D, C, R, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b1;
if (_TECHMAP_WIREINIT_Q_ !== 1'b0) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    wire Q_tmp;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(~D), .CLK(C), .ACLR(R), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q_tmp));
end else $error("Cannot implement a flip-flop with set that initialises to zero");
endmodule

module \$_DFF_NP1_ (input D, C, R, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b1;
if (_TECHMAP_WIREINIT_Q_ !== 1'b0) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    wire Q_tmp;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(~D), .CLK(~C), .ACLR(~R), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q_tmp));
    assign Q = ~Q_tmp;
end else $error("Cannot implement a flip-flop with set that initialises to zero");
endmodule

module \$_DFF_NN1_ (input D, C, R, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b1;
if (_TECHMAP_WIREINIT_Q_ !== 1'b0) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    wire Q_tmp;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(~D), .CLK(~C), .ACLR(R), .ENA(1'b1), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q_tmp));
    assign Q = ~Q_tmp;
end else $error("Cannot implement a flip-flop with set that initialises to zero");
endmodule

// D flip-flops with clock enable
module \$_DFFE_PP_ (input D, C, E, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(C), .ACLR(1'b1), .ENA(E), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop with enable that initialises to one");
endmodule

module \$_DFFE_PN_ (input D, C, E, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(C), .ACLR(1'b1), .ENA(~E), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop with enable that initialises to one");
endmodule

module \$_DFFE_NP_ (input D, C, E, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(~C), .ACLR(1'b1), .ENA(E), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop with enable that initialises to one");
endmodule

module \$_DFFE_NN_ (input D, C, E, output Q);
parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
if (_TECHMAP_WIREINIT_Q_ !== 1'b1) begin
    wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
    MISTRAL_FF _TECHMAP_REPLACE_(.DATAIN(D), .CLK(~C), .ACLR(1'b1), .ENA(~E), .SCLR(1'b0), .SLOAD(1'b0), .SDATA(1'b0), .Q(Q));
end else $error("Cannot implement a flip-flop with enable that initialises to one");
endmodule
