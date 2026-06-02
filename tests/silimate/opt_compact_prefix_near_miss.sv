module opt_compact_prefix_pack_passthrough (
  input  logic [7:0] sig,
  output logic [7:0] sig2
);
  always_comb begin
    sig2 = '0;
    for (int I = 0; I < 8; I++) begin
      if (sig[I])
        sig2[I] = sig[I];
    end
  end
endmodule

module opt_compact_prefix_pack_nonzero_init (
  input  logic [7:0] sig,
  output logic [7:0] sig2
);
  always_comb begin
    sig2 = '1;
    for (int I = 0, indx = 0; I < 8; I++) begin
      if (sig[I]) begin
        sig2[indx] = sig[I];
        indx += 1;
      end
    end
  end
endmodule

module opt_compact_prefix_pack_stride2 (
  input  logic [7:0] sig,
  output logic [7:0] sig2
);
  always_comb begin
    sig2 = '0;
    for (int I = 0, indx = 0; I < 4; I++) begin
      if (sig[I]) begin
        sig2[indx] = sig[I];
        indx += 2;
      end
    end
  end
endmodule

module opt_compact_prefix_sub_nonzero_init (
  input  logic [15:0] disable_in,
  input  logic [15:0] data_in,
  output logic [15:0] mask
);
  always_comb begin
    mask = '1;
    for (int I = 8, indx = 8; I > 0; I--) begin
      if (disable_in[I-1]) begin
        mask[I-1] = 1'b0;
      end else begin
        mask[I-1] = data_in[indx-1];
        indx = indx - 1;
      end
    end
  end
endmodule

module opt_compact_prefix_sub_stride2 (
  input  logic [15:0] disable_in,
  input  logic [15:0] data_in,
  output logic [15:0] mask
);
  always_comb begin
    mask = '0;
    for (int I = 8, indx = 16; I > 0; I--) begin
      if (disable_in[I-1]) begin
        mask[I-1] = 1'b0;
      end else begin
        mask[I-1] = data_in[indx-1];
        indx = indx - 2;
      end
    end
  end
endmodule
