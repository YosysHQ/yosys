//---------------------------------------
// 1-bit adder 
//---------------------------------------
(* abc9_box, lib_whitebox *)
module _fpga_adder(
    output sumout,
    output cout,
    input a,
    input b,
    input cin
);
    assign sumout = a ^ b ^ cin;
    assign cout = (a & b) | ((a | b) & cin);

endmodule
