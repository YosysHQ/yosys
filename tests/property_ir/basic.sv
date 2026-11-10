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
    ra: assert property ($rose(d) |=> q);
    fa: assert property ($fell(d) |=> !q);
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

module restrict_prop (input clk, input a, b, c);
    always @(posedge clk) begin
        restrict property (a |=> b);
        assert property (b ##1 c);
    end
endmodule

module multi_clk (input clk_a, clk_b, input c, d, e);
    property prop_a;
        @(posedge clk_a) c ##1 d;
    endproperty
    property prop_b;
        @(negedge clk_b) d ##1 e;
    endproperty
    assert property(prop_a and prop_b);
endmodule

module clock_ctrl (input a, b, c, d, input x, y);
    sequence seq;
        x ##1 y;
    endsequence

    a1: assert property (@(posedge a) seq);
    a2: assert property (@(negedge b) seq);
    a3: assert property (@(edge c) seq);
    a4: assert property (@(posedge a, negedge b) seq);
    a5: assert property (@(posedge c or negedge c) seq);
    a6: assert property (@(posedge c iff d) seq);
    a7: assert property (@(d) seq);
    a8: assert property (@(posedge a, d) seq);
endmodule

module recursive (input clk, input done, busy);
    property busy_until_done;
        done or (busy and (1'b1 |=> busy_until_done));
    endproperty

    assert property (@(posedge clk) busy_until_done);
endmodule

module global_clocking (input clk, input a, b);
    global clocking gclk @(posedge clk); endclocking
    assert property (@($global_clock) a |-> b);
endmodule

module assert_params (input clk, input a, b, c);
    property prop;
        @(posedge clk) a |-> ##1 b;
    endproperty;

    initial
        ia: assert property (prop);

    aa: assert property (prop);
    da: assert property (@(posedge clk) disable iff (c) a ##1 b);

    always @(posedge clk)
        if (c)
            ea: assert property (a |-> b);
endmodule

module clocked_disable (input clk, input a, b, c);
    property prop;
        @(posedge clk) a |-> ##1 b;
    endproperty;
    da: assert property (disable iff (c) prop);
endmodule
