module top;
    mid mid_uut ();
endmodule

module mid ();
    bot bot_uut ();
endmodule

module bot ();
    initial $display("%%l: %l\n%%m: %m");
    always $display("%%l: %l\n%%m: %m");
endmodule
