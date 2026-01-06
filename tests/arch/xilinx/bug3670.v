module bug3670(input we, output [31:0] o1, o2, output o3);
    // Completely missing port connections, where first affected port
    // (ADDRARDADDR) has a $setup delay
    RAMB36E1 ram1(.DOADO(o1));

    // Under-specified input port connections (WEA is 4 bits) which
    // has a $setup delay
    RAMB36E1 ram2(.WEA(we), .DOADO(o2));

    // Under-specified output port connections (DOADO is 32 bits)
    // with clk-to-q delay
    RAMB36E1 ram3(.DOADO(o3));
endmodule
