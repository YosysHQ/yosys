(* blackbox *)
module NX_CKS(CKI, CMD, CKO);
    input CKI;
    output CKO;
    input CMD;
    parameter ck_edge = 1'b0;
endmodule

