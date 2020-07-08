package p;

typedef struct packed {
    byte a;
    byte b;
} p_t;

typedef logic [31:0] l_t;

endpackage

module foo1(
	input p::p_t p,
	output p::p_t o
);
    assign o = p;
endmodule

module foo2(p, o);
    input p::p_t p;
    output p::p_t o;
    assign o = p;
endmodule

module foo3(input p::l_t p, input p::l_t o);
    assign o = p;
endmodule

module foo4(input logic [15:0] p, input logic [15:0] o);
    assign o = p;
endmodule

module test_parser(a,b,c,d,e,f,g,h,i);
input [7:0] a; // no explicit net declaration - net is unsigned
input [7:0] b;
input signed [7:0] c;
input signed [7:0] d; // no explicit net declaration - net is signed
output [7:0] e; // no explicit net declaration - net is unsigned
output [7:0] f;
output signed [7:0] g;
output signed [7:0] h; // no explicit net declaration - net is signed
output unsigned [7:0] i;
wire signed [7:0] b; // port b inherits signed attribute from net decl.
wire [7:0] c; // net c inherits signed attribute from port
logic signed [7:0] f;// port f inherits signed attribute from logic decl.
logic [7:0] g; // logic g inherits signed attribute from port

    assign a = 8'b10001111;
    assign b = 8'b10001111;
    assign c = 8'b10001111;
    assign d = 8'b10001111;
    assign e = 8'b10001111;
    assign f = 8'b10001111;
    assign g = 8'b10001111;
    assign h = 8'b10001111;
    assign i = 8'b10001111;
    always_comb begin
        assert($unsigned(143) == a);
        assert($signed(-113) == b);
        assert($signed(-113) == c);
        assert($signed(-113) == d);
        assert($unsigned(143) == e);
        assert($unsigned(143) == f);
        assert($signed(-113) == g);
        assert($signed(-113) == h);
        assert($unsigned(143) == i);
    end
endmodule

module top;
    p::p_t ps;
    assign ps.a = 8'hAA;
    assign ps.b = 8'h55;
    foo1 foo(.p(ps));

    p::p_t body;
    assign body.a = 8'hBB;
    assign body.b = 8'h66;
    foo2 foo_b(.p(body));

    typedef p::l_t local_alias;

    local_alias l_s;
    assign l_s = 32'hAAAAAAAA;
    foo3 foo_l(.p(l_s));

    typedef logic [15:0] sl_t;

    sl_t sl_s;
    assign sl_s = 16'hBBBB;
    foo4 foo_sl(.p(sl_s));

    typedef sl_t local_alias_st;

    local_alias_st lsl_s;
    assign lsl_s = 16'hCCCC;
    foo4 foo_lsl(.p(lsl_s));

    const logic j = 1'b1;

    always_comb begin
        assert(8'hAA == ps.a);
        assert(8'h55 == ps.b);
        assert(8'hBB == body.a);
        assert(8'h66 == body.b);
        assert(32'hAAAAAAAA == l_s);
        assert(16'hBBBB == sl_s);
        assert(16'hCCCC == lsl_s);
        assert(1'b1 == j);
    end
endmodule
