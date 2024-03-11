(* blackbox *)
module NX_GCK_U(SI1, SI2, CMD, SO);
    input CMD;
    input SI1;
    input SI2;
    output SO;
    parameter inv_in = 1'b0;
    parameter inv_out = 1'b0;
    parameter std_mode = "BYPASS";
endmodule
