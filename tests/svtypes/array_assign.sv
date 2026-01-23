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
endmodule
