module opt_compact_prefix_multi_match (
  input  logic [7:0] sig,
  output logic [7:0] sig2
);
  always_comb begin
    sig2 = '0;
    for (int I = 0, indx = 0; I < 8; I++) begin
      if (sig[I]) begin
        sig2[indx] = sig[I];
        indx += 1;
      end
    end
  end
endmodule

module opt_compact_prefix_multi_keep (
  input  logic       sel,
  input  logic [7:0] a,
  input  logic [7:0] b,
  output logic [7:0] y
);
  assign y = sel ? a : b;
endmodule
