// Modulo-n decimation loops: scanning the enable vector, mark every n-th
// enabled bit. Exercised by opt_compact_prefix's modulo decimation rewrite
// (cf. the qor_spi_ra_add_chain2 regression).

module opt_compact_prefix_mod8 (
  input  logic [7:0] en,
  input  logic [3:0] n,
  output logic [7:0] mask
);
  always_comb begin
    mask = '0;
    for (int I = 7, cnt = 0; I >= 0; I--) begin
      if (en[I] && (n > 0)) begin
        if (cnt == (n - 1)) begin
          mask[I] = 1'b1;
          cnt     = 0;
        end else begin
          cnt++;
        end
      end
    end
  end
endmodule

module opt_compact_prefix_mod16 (
  input  logic [15:0] en,
  input  logic [4:0]  n,
  output logic [15:0] mask
);
  always_comb begin
    mask = '0;
    for (int I = 15, cnt = 0; I >= 0; I--) begin
      if (en[I] && (n > 0)) begin
        if (cnt == (n - 1)) begin
          mask[I] = 1'b1;
          cnt     = 0;
        end else begin
          cnt++;
        end
      end
    end
  end
endmodule

// Same function, but scanned LSB-first (exercises the mirrored direction).
module opt_compact_prefix_mod_lsb8 (
  input  logic [7:0] en,
  input  logic [3:0] n,
  output logic [7:0] mask
);
  always_comb begin
    mask = '0;
    for (int I = 0, cnt = 0; I < 8; I++) begin
      if (en[I] && (n > 0)) begin
        if (cnt == (n - 1)) begin
          mask[I] = 1'b1;
          cnt     = 0;
        end else begin
          cnt++;
        end
      end
    end
  end
endmodule

// Negative near-miss: marks every (n+1)-th enabled bit (reset on cnt == n),
// a different function that must NOT be rewritten.
module opt_compact_prefix_mod_offbyone (
  input  logic [7:0] en,
  input  logic [3:0] n,
  output logic [7:0] mask
);
  always_comb begin
    mask = '0;
    for (int I = 7, cnt = 0; I >= 0; I--) begin
      if (en[I] && (n > 0)) begin
        if (cnt == n) begin
          mask[I] = 1'b1;
          cnt     = 0;
        end else begin
          cnt++;
        end
      end
    end
  end
endmodule
