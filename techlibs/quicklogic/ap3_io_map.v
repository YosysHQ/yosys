module \$__out_buff (Q, A);
	output Q;
    input A;

    out_buff _TECHMAP_REPLACE_ (.Q(Q), .A(A));
endmodule

module \$__in_buff (Q, A);
	output Q;
    input A;

    in_buff _TECHMAP_REPLACE_ (.Q(Q), .A(A));

endmodule