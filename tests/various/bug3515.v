// Triple AND GATE
module mod_74x08_3 (
    input A_1,
    input B_1,
    input A_2,
    input B_2,
    input A_3,
    input B_3,
    output Y_1,
    output Y_2,
    output Y_3);

assign Y_1 = A_1 & B_1;
assign Y_2 = A_2 & B_2;
assign Y_3 = A_3 & B_3;

endmodule

// OR GATE
module mod_74x32_1 (
    input A_1,
    input B_1,
    output Y_1);

assign Y_1 = A_1 | B_1;
endmodule
