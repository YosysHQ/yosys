module a(Q);
    output wire Q;

    assign Q = 0;
endmodule

module b(D);
    input wire D;
endmodule

module c;
    wor D;
    assign D = 1;
    assign D = 0;
    assign D = 1;
    assign D = 0;


    wand E;
    
    genvar i;
    for (i = 0; i < 3; i = i + 1)
    begin :genloop
        a a_inst (
            .Q(E)
        );
        
        b b_inst (
            .D(E)
        );
    end

endmodule

