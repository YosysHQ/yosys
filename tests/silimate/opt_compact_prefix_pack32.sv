module opt_compact_prefix_pack32 (
  input  logic [31:0] sig,
  output logic [31:0] sig2
);
  always_comb begin
    sig2 = '0;
    for (int I = 0, indx = 0; I < 32; I++) begin
      if (sig[I]) begin
        sig2[indx] = sig[I];
        indx += 1;
      end
    end
  end
endmodule
