module opt_compact_prefix_pack_renamed (
  input  logic [7:0] in_bits,
  output logic [7:0] packed_bits
);
  always_comb begin
    packed_bits = '0;
    for (int I = 0, indx = 0; I < 8; I++) begin
      if (in_bits[I]) begin
        packed_bits[indx] = in_bits[I];
        indx += 1;
      end
    end
  end
endmodule

module opt_compact_prefix_sub_renamed (
  input  logic [15:0] stall_vec,
  input  logic [15:0] payload_vec,
  output logic [15:0] allow_mask
);
  always_comb begin
    allow_mask = '0;
    for (int I = 8, indx = 8; I > 0; I--) begin
      if (stall_vec[I-1]) begin
        allow_mask[I-1] = 1'b0;
      end else begin
        allow_mask[I-1] = payload_vec[indx-1];
        indx = indx - 1;
      end
    end
  end
endmodule
