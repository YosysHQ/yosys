(* abc9_box, lib_whitebox *)
module soft_adder (
    (* abc9_carry *)
    output CO,
    output O,
    input A, B,
    (* abc9_carry *)
    input CI,
    input I2, I3
);
    parameter LUT = 0;
    parameter I2_IS_CI = 0;

    // Effective LUT input
    wire [3:0] li = (I2_IS_CI) ? {I3, CI, B, A} : {I3, I2, B, A};

    // Output function
    wire [7:0] s1 = li[0] ?
        {LUT[15], LUT[13], LUT[11], LUT[9], LUT[7], LUT[5], LUT[3], LUT[1]} :
        {LUT[14], LUT[12], LUT[10], LUT[8], LUT[6], LUT[4], LUT[2], LUT[0]};

    wire [3:0] s2 = li[1] ? {s1[7], s1[5], s1[3], s1[1]} :
                            {s1[6], s1[4], s1[2], s1[0]};

    wire [1:0] s3 = li[2] ? {s2[3], s2[1]} : {s2[2], s2[0]};

    assign      O = li[3] ? s3[1] : s3[0];

    // Carry out function
    assign CO = (s2[2]) ? CI : s2[3];

endmodule
