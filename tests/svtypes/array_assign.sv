// Test for array-to-array assignment and ternary expressions

`define STRINGIFY(x) `"x`"
`define STATIC_ASSERT(x) if(!(x)) $error({"assert failed: ", `STRINGIFY(x)})

module top;
    // Test 1: Basic array ternary with continuous assignment
    reg [7:0] a1[4];
    reg [7:0] b1[4];
    wire [7:0] out1[4];
    wire sel1;
    assign out1 = sel1 ? a1 : b1;
    `STATIC_ASSERT($bits(out1) == 32);

    // Test 2: Non-zero base index
    reg [7:0] a2[3:6];
    reg [7:0] b2[3:6];
    wire [7:0] out2[3:6];
    wire sel2;
    assign out2 = sel2 ? a2 : b2;
    `STATIC_ASSERT($bits(out2) == 32);

    // Test 3: Single-bit elements
    reg a3[8];
    reg b3[8];
    wire out3[8];
    wire sel3;
    assign out3 = sel3 ? a3 : b3;
    `STATIC_ASSERT($bits(out3) == 8);

    // Test 4: Multi-dimensional array ternary
    reg [7:0] a4[2][3];
    reg [7:0] b4[2][3];
    wire [7:0] out4[2][3];
    wire sel4;
    assign out4 = sel4 ? a4 : b4;
    `STATIC_ASSERT($bits(out4) == 48);

    // Test 5: Direct array assignment (continuous)
    reg [7:0] a5[4];
    wire [7:0] b5[4];
    assign b5 = a5;
    `STATIC_ASSERT($bits(b5) == 32);

    // Test 6: Multi-dimensional direct assignment (continuous)
    reg [7:0] a6[2][3];
    wire [7:0] b6[2][3];
    assign b6 = a6;
    `STATIC_ASSERT($bits(b6) == 48);

    // Test 7: Procedural direct assignment with different unpacked index ranges
    // Covers the AST_BLOCK expansion path for AST_ASSIGN_EQ.
    logic pa [1:0][1:0];
    logic pb [1:0][0:1];
    always_comb begin
        pa[0][0] = 1'b0;
        pa[0][1] = 1'b1;
        pa[1][0] = 1'b1;
        pa[1][1] = 1'b1;

        pb = pa;

        assert(pb[0][1] == 1'b0);
        assert(pb[0][0] == 1'b1);
        assert(pb[1][1] == 1'b1);
        assert(pb[1][0] == 1'b1);
    end

    // Test 8: Procedural ternary assignment on arrays
    // Covers the AST_BLOCK expansion path for ternary RHS.
    logic pt_a [1:0];
    logic pt_b [1:0];
    logic pt_o [1:0];
    logic pt_sel;
    always_comb begin
        pt_a[0] = 1'b0;
        pt_a[1] = 1'b1;
        pt_b[0] = 1'b1;
        pt_b[1] = 1'b0;
        pt_sel = 1'b1;

        pt_o = pt_sel ? pt_a : pt_b;

        assert(pt_o[0] == 1'b0);
        assert(pt_o[1] == 1'b1);
    end

    // Test 9: Positional assignment pattern on a whole unpacked array
    // Covers the parser and continuous assignment expansion path for `'{...}.
    wire ap_table [1];
    wire ap_i = 1'b0;
    wire ap_out;
    assign ap_table = '{1'h1};
    assign ap_out = ap_table[ap_i > 1'h0 ? 1'h0 : ap_i];
    always_comb begin
        assert(ap_out == 1'b1);
    end

    // Test 10: Positional assignment pattern preserves left-to-right element order.
    wire ap_order [2];
    assign ap_order = '{1'b0, 1'b1};
    always_comb begin
        assert(ap_order[0] == 1'b0);
        assert(ap_order[1] == 1'b1);
    end

    function automatic logic ap_identity(input logic value);
        ap_identity = value;
    endfunction

    // Test 11: The first assignment pattern element is a runtime expression.
    wire ap_runtime_in = 1'b1;
    wire ap_runtime [2];
    assign ap_runtime = '{ap_identity(ap_runtime_in), 1'b0};
    always_comb begin
        assert(ap_runtime[0] == 1'b1);
        assert(ap_runtime[1] == 1'b0);
    end

    // Test 12: Nested positional assignment pattern on a multidimensional array.
    wire ap_nested [2][2];
    assign ap_nested = '{'{1'b1, 1'b0}, '{1'b0, 1'b1}};
    always_comb begin
        assert(ap_nested[0][0] == 1'b1);
        assert(ap_nested[0][1] == 1'b0);
        assert(ap_nested[1][0] == 1'b0);
        assert(ap_nested[1][1] == 1'b1);
    end

    // Test 13: Multidimensional assignment pattern with row expressions.
    wire ap_row0 [2];
    wire ap_row1 [2];
    wire ap_rows [2][2];
    assign ap_row0 = '{1'b1, 1'b0};
    assign ap_row1 = '{1'b0, 1'b1};
    assign ap_rows = '{ap_row0, ap_row1};
    always_comb begin
        assert(ap_rows[0][0] == 1'b1);
        assert(ap_rows[0][1] == 1'b0);
        assert(ap_rows[1][0] == 1'b0);
        assert(ap_rows[1][1] == 1'b1);
    end

    // Test 14: Procedural blocking assignment pattern preserves RHS values.
    logic ap_swap [2];
    always_comb begin
        ap_swap[0] = 1'b0;
        ap_swap[1] = 1'b1;
        ap_swap = '{ap_swap[1], ap_swap[0]};

        assert(ap_swap[0] == 1'b1);
        assert(ap_swap[1] == 1'b0);
    end

    // Test 15: Assignment pattern elements use the target element width context.
    logic [4:0] ap_width_ctx [1];
    assign ap_width_ctx = '{4'hf + 4'h1};
    always_comb begin
        assert(ap_width_ctx[0] == 5'h10);
    end

    // Test 16: Nested assignment pattern elements also use the target element width context.
    logic [4:0] ap_nested_width_ctx [1][1];
    assign ap_nested_width_ctx = '{'{4'hf + 4'h1}};
    always_comb begin
        assert(ap_nested_width_ctx[0][0] == 5'h10);
    end
endmodule
