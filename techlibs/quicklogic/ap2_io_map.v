module \$__out_buff (Q, A);
	output Q;
    input A;

    parameter _TECHMAP_CONSTMSK_A = 0;
    parameter _TECHMAP_CONSTVAL_A = 0;

    if(_TECHMAP_CONSTMSK_A == 1'b1) begin
        d_buff _TECHMAP_REPLACE_ (.Q(Q), .EN(_TECHMAP_CONSTVAL_A));
    end
    else begin
        out_buff _TECHMAP_REPLACE_ (.Q(Q), .A(A));
    end

endmodule

module \$__in_buff (Q, A);
	output Q;
    input A;

    in_buff _TECHMAP_REPLACE_ (.Q(Q), .A(A));

endmodule