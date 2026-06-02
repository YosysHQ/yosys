module opt_compact_prefix_sub16 (
  input  logic [31:0] disable_in,
  input  logic [31:0] data_in,
  output logic [31:0] mask
);
  always_comb begin
    mask = '0;
    for (int I = 16, indx = 16; I > 0; I--) begin
      if (disable_in[I-1]) begin
        mask[I-1] = 1'b0;
      end else begin
        mask[I-1] = data_in[indx-1];
        indx = indx - 1;
      end
    end
  end
endmodule
