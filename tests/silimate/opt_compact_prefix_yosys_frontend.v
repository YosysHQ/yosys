module opt_compact_prefix_yosys_pack (
  input  wire [7:0] in_bits,
  output reg  [7:0] packed_bits
);
  integer I;
  integer indx;
  always @* begin
    packed_bits = 8'b0;
    indx = 0;
    for (I = 0; I < 8; I = I + 1) begin
      if (in_bits[I]) begin
        packed_bits[indx] = in_bits[I];
        indx = indx + 1;
      end
    end
  end
endmodule

module opt_compact_prefix_yosys_sub (
  input  wire [15:0] stall_vec,
  input  wire [15:0] payload_vec,
  output reg  [15:0] allow_mask
);
  integer I;
  integer indx;
  always @* begin
    allow_mask = 16'b0;
    indx = 8;
    for (I = 8; I > 0; I = I - 1) begin
      if (stall_vec[I-1]) begin
        allow_mask[I-1] = 1'b0;
      end else begin
        allow_mask[I-1] = payload_vec[indx-1];
        indx = indx - 1;
      end
    end
  end
endmodule
