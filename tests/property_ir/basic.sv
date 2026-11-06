module top (input clk, input a, b, c);
    property p;
        a ##1 b |-> always(c);
    endproperty
    inline: assert property (@(posedge clk) a ##1 b |-> always(c));
    always @(posedge clk) begin
        ap: assert property (p);
        se: assert property (s_eventually [2:$] a);
    end
endmodule

module next (input clk, input a, b);
    always @(posedge clk) begin
        assert property (nexttime[2] b);
    end
endmodule

module rep (input clk, input a, b, c);
    sequence s;
        a ##1 (b [=3]) ##1 c;
    endsequence

    always @(posedge clk) begin
        zp0: assert property (##0 c);
        zp1: assert property (##1 c);
        zp2: assert property (##2 c);
        ap0: assert property (a ##0 c);
        ap1: assert property (a ##1 c);
        ap2: assert property (a ##2 c);
        sp: assert property (s);
    end
endmodule

module ite (input clk, input a, b, c);
    property p;
        @(posedge clk)
            if (a)
                b ##1 c
            else
                c ##1 b;
    endproperty

    assert property (p);
endmodule

module nested (input clk, input a, b, c);
    sequence p;
        a ##1 b;
    endsequence
    sequence q;
        p ##1 c;
    endsequence
    ap: assert property (@(posedge clk) q);
endmodule

module immediate (input clk, input a);
    always @(posedge clk) begin
        assert (a);
    end
endmodule

module sampled_val (input clk, input a, b);
    always @(posedge clk) begin
        assert property ($rose(a) |=> b);
    end
endmodule

module submod (input clk, input a, b, c);
    property p;
        a ##1 b |-> always(c);
    endproperty

    inner: assert property (@(posedge clk) p);
endmodule

module mod (input clk, input a, b, c);
    property p;
        a |-> s_eventually [1:2] b;
    endproperty

    submod sub (clk, a, b, c);

    outer: assert property (@(posedge clk) p);
endmodule

module flopped (input clk, input d);
    reg q;
    always @(posedge clk)
        q <= d;

    default clocking @(posedge clk); endclocking
    assert property ($rose(d) |=> q);
    assert property ($fell(d) |=> !q);
endmodule

module binops (input clk, input a, b, c);
    property q;
        b |-> c;
    endproperty

    sequence s;
        a ##[2:4] b;
    endsequence

    sequence t;
        s or c[*1:3];
    endsequence

    always @(posedge clk) begin
        assert property ((a #-# b) and not q);
        assert property (a && b throughout t);
    end
endmodule
