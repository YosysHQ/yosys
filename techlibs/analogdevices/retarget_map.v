module FF (input C, D, output Q);
parameter INIT = 1'b0;
if (INIT === 1'b1) begin
FFPE _TECHMAP_REPLACE_ (.C(C), .D(D), .PRE(1'b0), .CE(1'b1), .Q(Q));
end else begin
FFCE _TECHMAP_REPLACE_ (.C(C), .D(D), .CLR(1'b0), .CE(1'b1), .Q(Q));
end
endmodule

module FF_N (input C, D, output Q);
parameter INIT = 1'b0;
if (INIT === 1'b1) begin
FFPE_N _TECHMAP_REPLACE_ (.C(C), .D(D), .PRE(1'b0), .CE(1'b1), .Q(Q));
end else begin
FFCE_N _TECHMAP_REPLACE_ (.C(C), .D(D), .CLR(1'b0), .CE(1'b1), .Q(Q));
end
endmodule

module FFC (input C, D, CLR, output Q);
FFCE _TECHMAP_REPLACE_ (.C(C), .D(D), .CLR(CLR), .CE(1'b1), .Q(Q));
endmodule

module FFC_N (input C, D, CLR, output Q);
FFCE_N _TECHMAP_REPLACE_ (.C(C), .D(D), .CLR(CLR), .CE(1'b1), .Q(Q));
endmodule

module FFP (input C, D, PRE, output Q);
FFPE _TECHMAP_REPLACE_ (.C(C), .D(D), .PRE(PRE), .CE(1'b1), .Q(Q));
endmodule

module FFP_N (input C, D, CLR, output Q);
FFPE_N _TECHMAP_REPLACE_ (.C(C), .D(D), .PRE(PRE), .CE(1'b1), .Q(Q));
endmodule

module FFR (input C, D, R, output Q);
FFRE _TECHMAP_REPLACE_ (.C(C), .D(D), .R(R), .CE(1'b1), .Q(Q));
endmodule

module FFR_N (input C, D, R, output Q);
FFRE_N _TECHMAP_REPLACE_ (.C(C), .D(D), .R(R), .CE(1'b1), .Q(Q));
endmodule

module FFS (input C, D, S, output Q);
FFSE _TECHMAP_REPLACE_ (.C(C), .D(D), .S(S), .CE(1'b1), .Q(Q));
endmodule

module FFS_N (input C, D, S, output Q);
FFSE_N _TECHMAP_REPLACE_ (.C(C), .D(D), .S(S), .CE(1'b1), .Q(Q));
endmodule
