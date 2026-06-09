module opt_argmax_basic (
  input  wire [15:0]      sig,
  input  wire [15:0][3:0] sig3,
  input  wire [15:0][7:0] sig2,
  output reg  [3:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 16; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_w8 (
  input  wire [7:0]       sig,
  input  wire [7:0][2:0]  sig3,
  input  wire [7:0][4:0]  sig2,
  output reg  [2:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 8; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_w32 (
  input  wire [31:0]      sig,
  input  wire [31:0][4:0] sig3,
  input  wire [31:0][5:0] sig2,
  output reg  [4:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 32; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_identity_w8 (
  input  wire [7:0]       valid_in,
  input  wire [7:0][4:0]  val_in,
  output reg  [2:0]       best_idx
);
  always_comb begin
    best_idx = '0;
    for (int k = 1; k < 8; k++) begin
      if (!valid_in[best_idx] && valid_in[k]) begin
        best_idx = k;
      end else if (valid_in[best_idx] && valid_in[k] &&
                   (val_in[best_idx] < val_in[k])) begin
        best_idx = k;
      end
    end
  end
endmodule

module opt_argmax_identity_w16 (
  input  wire [15:0]      valid_in,
  input  wire [15:0][7:0] val_in,
  output reg  [3:0]       best_idx
);
  always_comb begin
    best_idx = '0;
    for (int k = 1; k < 16; k++) begin
      if (!valid_in[best_idx] && valid_in[k]) begin
        best_idx = k;
      end else if (valid_in[best_idx] && valid_in[k] &&
                   (val_in[best_idx] < val_in[k])) begin
        best_idx = k;
      end
    end
  end
endmodule

module opt_argmax_flat (
  input  wire [7:0]       sig,
  input  wire [23:0]      sig3,
  input  wire [39:0]      sig2,
  output reg  [2:0]       se_target_idx
);
  function automatic [2:0] idx_at(input [2:0] pos);
    idx_at = sig3[pos * 3 +: 3];
  endfunction

  function automatic [4:0] val_at(input [2:0] pos);
    val_at = sig2[idx_at(pos) * 5 +: 5];
  endfunction

  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 8; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (val_at(se_target_idx) < val_at(k[2:0]))) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_value_w1 (
  input  wire [7:0]       sig,
  input  wire [7:0][2:0]  sig3,
  input  wire [7:0]       sig2,
  output reg  [2:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 8; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_value_w16 (
  input  wire [7:0]        sig,
  input  wire [7:0][2:0]   sig3,
  input  wire [7:0][15:0]  sig2,
  output reg  [2:0]        se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 8; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_two_regions (
  input  wire [7:0]       sig_a,
  input  wire [7:0][2:0]  sig3_a,
  input  wire [7:0][7:0]  sig2_a,
  input  wire [7:0]       sig_b,
  input  wire [7:0][2:0]  sig3_b,
  input  wire [7:0][5:0]  sig2_b,
  output reg  [2:0]       idx_a,
  output reg  [2:0]       idx_b
);
  always_comb begin
    idx_a = '0;
    for (int k = 1; k < 8; k++) begin
      if (!sig_a[idx_a] && sig_a[k]) begin
        idx_a = k;
      end else if (sig_a[idx_a] && sig_a[k] &&
                   (sig2_a[sig3_a[idx_a]] < sig2_a[sig3_a[k]])) begin
        idx_a = k;
      end
    end

    idx_b = '0;
    for (int k = 1; k < 8; k++) begin
      if (!sig_b[idx_b] && sig_b[k]) begin
        idx_b = k;
      end else if (sig_b[idx_b] && sig_b[k] &&
                   (sig2_b[sig3_b[idx_b]] < sig2_b[sig3_b[k]])) begin
        idx_b = k;
      end
    end
  end
endmodule

module opt_argmax_shared_consumer (
  input  wire [7:0]       sig,
  input  wire [7:0][2:0]  sig3,
  input  wire [7:0][7:0]  sig2,
  input  wire [2:0]       salt,
  output reg  [2:0]       se_target_idx,
  output wire [2:0]       also_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 8; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end

  assign also_idx = se_target_idx ^ salt;
endmodule

module opt_argmax_tie_high (
  input  wire [15:0]      sig,
  input  wire [15:0][3:0] sig3,
  input  wire [15:0][7:0] sig2,
  output reg  [3:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 16; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] <= sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_nonzero_default (
  input  wire [15:0]      sig,
  input  wire [15:0][3:0] sig3,
  input  wire [15:0][7:0] sig2,
  output reg  [3:0]       se_target_idx
);
  always_comb begin
    se_target_idx = 4'd1;
    for (int k = 1; k < 16; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_min (
  input  wire [15:0]      sig,
  input  wire [15:0][3:0] sig3,
  input  wire [15:0][7:0] sig2,
  output reg  [3:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 16; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] > sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_w12 (
  input  wire [11:0]      sig,
  input  wire [11:0][3:0] sig3,
  input  wire [11:0][7:0] sig2,
  output reg  [3:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 12; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_bad_index_width (
  input  wire [15:0]      sig,
  input  wire [15:0][4:0] sig3,
  input  wire [15:0][7:0] sig2,
  output reg  [3:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 16; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx][3:0]] < sig2[sig3[k][3:0]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_stress_noop (
  input  wire [63:0] sel,
  input  wire [63:0] a,
  input  wire [63:0] b,
  output wire [63:0] y
);
  wire [63:0] mux0 = sel[0] ? a : b;
  wire [63:0] mux1 = sel[1] ? mux0 : {mux0[31:0], mux0[63:32]};
  wire [63:0] mux2 = sel[2] ? mux1 : (mux1 ^ a);
  wire [63:0] mux3 = sel[3] ? mux2 : (mux2 & b);
  wire [63:0] mux4 = sel[4] ? mux3 : (mux3 | a);
  wire [63:0] mux5 = sel[5] ? mux4 : {mux4[47:0], mux4[63:48]};
  assign y = sel[6] ? mux5 : ~mux5;
endmodule

module opt_argmax_unrelated (
  input  wire [3:0] a,
  input  wire [3:0] b,
  input  wire       sel,
  output wire [3:0] y
);
  assign y = sel ? a : b;
endmodule

module opt_argmax_multi_match (
  input  wire [15:0]      sig,
  input  wire [15:0][3:0] sig3,
  input  wire [15:0][7:0] sig2,
  output reg  [3:0]       se_target_idx
);
  always_comb begin
    se_target_idx = '0;
    for (int k = 1; k < 16; k++) begin
      if (!sig[se_target_idx] && sig[k]) begin
        se_target_idx = k;
      end else if (sig[se_target_idx] && sig[k] &&
                   (sig2[sig3[se_target_idx]] < sig2[sig3[k]])) begin
        se_target_idx = k;
      end
    end
  end
endmodule

module opt_argmax_multi_keep (
  input  wire [3:0] a,
  input  wire [3:0] b,
  input  wire       sel,
  output wire [3:0] y
);
  assign y = sel ? a : b;
endmodule
