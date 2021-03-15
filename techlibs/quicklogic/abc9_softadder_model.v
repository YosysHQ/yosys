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
    wire [0:3] li = (I2_IS_CI) ? {A, B, CI, I3} : {A, B, I2, I3};

    // Output function
    wire [0:7] s1 = li[0] ?
        {LUT[1], LUT[3], LUT[5], LUT[7], LUT[9], LUT[11], LUT[13], LUT[15]}:
        {LUT[0], LUT[2], LUT[4], LUT[6], LUT[8], LUT[10], LUT[12], LUT[14]};

    wire [0:3] s2 = li[1] ? {s1[1], s1[3], s1[5], s1[7]} :
                            {s1[0], s1[2], s1[4], s1[6]};

    wire [0:1] s3 = li[2] ? {s2[1], s2[3]} : {s2[0], s2[2]};

    assign      O = li[3] ? s3[1] : s3[0];
    
    // Carry out function
    assign CO = (s2[2]) ? CI : s2[3];

endmodule

