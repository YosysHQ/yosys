module test_001(clk, a, a_old, b);
    // test case taken from:
    // http://www.reddit.com/r/yosys/comments/1wvpj6/trouble_with_assertions_and_sat_solver/

    input wire clk;
    input wire a;

    output reg a_old = 0;
    output reg b = 1;
    wire assertion = (a_old != b);

    always @(posedge clk) begin
        a_old <= a;
        b <= !a;

        assert(a_old != b);
    end
endmodule

module test_002(clk, a, a_old, b);
    // copy from test_001 with modifications

    input wire clk;
    input wire a;

    output reg a_old = 0;
    output reg b = 0;  // <-- this will fail
    wire assertion = (a_old != b);

    always @(posedge clk) begin
        a_old <= a;
        b <= !a;
        assert(a_old != b);
    end
endmodule

module test_003(clk, a, a_old, b);
    // copy from test_001 with modifications

    input wire clk;
    input wire a;

    output reg a_old = 0;
    output reg b;  // <-- this will fail
    wire assertion = (a_old != b);

    always @(posedge clk) begin
        a_old <= a;
        b <= !a;
        assert(a_old != b);
    end
endmodule

module test_004(clk, a, a_old, b);
    // copy from test_001 with modifications

    input wire clk;
    input wire a;

    output reg a_old = 0;
    output reg b = 1;
    wire assertion = (a_old != b);

    always @(posedge clk) begin
        a_old <= a;
        b <= !a;
        assert(a_old == b);  // <-- this will fail
    end
endmodule

module test_005(clk, a, a_old, b);
    // copy from test_001 with modifications

    input wire clk;
    input wire a;

    output reg a_old = 1; // <-- inverted, no problem
    output reg b = 0;
    wire assertion = (a_old != b);

    always @(posedge clk) begin
        a_old <= a;
        b <= !a;
        assert(a_old != b);
    end
endmodule

