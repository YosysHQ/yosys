// Test designs for opt_priority_onehot.
//
// Each "positive" module computes a lowest/highest-index priority select of a
// per-lane index field and scatters the winning field into a one-hot output,
// mirroring the qor_spi_ra_binary_tree shape. The "negative" modules look
// similar but compute a different function and must be left untouched.

// Main shape: N=16 lanes, 5-bit id lanes, 4-bit field id[*][4:1], LSB-first.
module pri_onehot_basic (
  input  wire [15:0]      req,
  input  wire [15:0][4:0] id,
  output reg  [15:0]      oneh
);
  always_comb begin
    reg [15:0] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 0; I < 16; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][4:1]] |= sel[I];
    end
  end
endmodule

// One-based ports [N:1] / id[I][IDX_W:1], matching the qor_spi_ra_binary_tree
// regression exactly (Verific splits id into id[1]..id[16]).
module pri_onehot_onebased (
  input  wire [16:1]      req,
  input  wire [16:1][4:0] id,
  output reg  [15:0]      oneh
);
  always_comb begin
    reg [16:1] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 1; I <= 16; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][4:1]] |= sel[I];
    end
  end
endmodule

// Packed field: no per-lane gap (ID_W == IDX_W == 4), field id[*][3:0].
module pri_onehot_packed (
  input  wire [15:0]      req,
  input  wire [15:0][3:0] id,
  output reg  [15:0]      oneh
);
  always_comb begin
    reg [15:0] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 0; I < 16; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][3:0]] |= sel[I];
    end
  end
endmodule

// Scaled down: N=8, 4-bit id lanes, 3-bit field id[*][3:1], W=8.
module pri_onehot_w8 (
  input  wire [7:0]      req,
  input  wire [7:0][3:0] id,
  output reg  [7:0]      oneh
);
  always_comb begin
    reg [7:0] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 0; I < 8; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][3:1]] |= sel[I];
    end
  end
endmodule

// Scaled up: N=32, 6-bit id lanes, 5-bit field id[*][5:1], W=32.
module pri_onehot_w32 (
  input  wire [31:0]      req,
  input  wire [31:0][5:0] id,
  output reg  [31:0]      oneh
);
  always_comb begin
    reg [31:0] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 0; I < 32; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][5:1]] |= sel[I];
    end
  end
endmodule

// Lane count != output width: N=8 lanes, 4-bit field, W=16.
module pri_onehot_n8_w16 (
  input  wire [7:0]      req,
  input  wire [7:0][4:0] id,
  output reg  [15:0]     oneh
);
  always_comb begin
    reg [7:0] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 0; I < 8; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][4:1]] |= sel[I];
    end
  end
endmodule

// MSB-first priority: highest set index wins (W=8 to keep SAT cheap).
module pri_onehot_msb (
  input  wire [7:0]      req,
  input  wire [7:0][3:0] id,
  output reg  [7:0]      oneh
);
  always_comb begin
    reg [7:0] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 7; I >= 0; I--) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][3:1]] |= sel[I];
    end
  end
endmodule

// Two independent priority-onehot regions in one module.
module pri_onehot_two_regions (
  input  wire [7:0]      req_a,
  input  wire [7:0][3:0] id_a,
  input  wire [7:0]      req_b,
  input  wire [7:0][3:0] id_b,
  output reg  [7:0]      oneh_a,
  output reg  [7:0]      oneh_b
);
  always_comb begin
    reg [7:0] acc, sel;
    acc = '0; sel = '0; oneh_a = '0;
    for (int I = 0; I < 8; I++) begin
      sel[I] = req_a[I] & ~(|acc);
      acc[I] = req_a[I];
      oneh_a[id_a[I][3:1]] |= sel[I];
    end
  end
  always_comb begin
    reg [7:0] acc2, sel2;
    acc2 = '0; sel2 = '0; oneh_b = '0;
    for (int I = 0; I < 8; I++) begin
      sel2[I] = req_b[I] & ~(|acc2);
      acc2[I] = req_b[I];
      oneh_b[id_b[I][3:1]] |= sel2[I];
    end
  end
endmodule

// One-hot output also consumed by a downstream parity output.
module pri_onehot_shared_consumer (
  input  wire [7:0]      req,
  input  wire [7:0][3:0] id,
  output reg  [7:0]      oneh,
  output wire            par
);
  always_comb begin
    reg [7:0] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 0; I < 8; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][3:1]] |= sel[I];
    end
  end
  assign par = ^oneh;
endmodule

// ---------------------------------------------------------------------------
// Negative / near-miss modules: must NOT be rewritten.
// ---------------------------------------------------------------------------

// No priority: OR of all decoded fields (output is generally not one-hot).
module pri_onehot_orall (
  input  wire [15:0]      req,
  input  wire [15:0][4:0] id,
  output reg  [15:0]      oneh
);
  always_comb begin
    oneh = '0;
    for (int I = 0; I < 16; I++)
      oneh[id[I][4:1]] |= req[I];
  end
endmodule

// Nonzero default when no request: function is not "0 when all-invalid".
module pri_onehot_nonzero_default (
  input  wire [15:0]      req,
  input  wire [15:0][4:0] id,
  output reg  [15:0]      oneh
);
  always_comb begin
    reg [15:0] acc, sel;
    acc = '0; sel = '0; oneh = '1;
    for (int I = 0; I < 16; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][4:1]] |= sel[I];
    end
  end
endmodule

// Non-power-of-two output width.
module pri_onehot_nonpow2 (
  input  wire [11:0]      req,
  input  wire [11:0][3:0] id,
  output reg  [11:0]      oneh
);
  always_comb begin
    reg [11:0] acc, sel;
    acc = '0; sel = '0; oneh = '0;
    for (int I = 0; I < 12; I++) begin
      sel[I] = req[I] & ~(|acc);
      acc[I] = req[I];
      oneh[id[I][3:1]] |= sel[I];
    end
  end
endmodule

// Unrelated mux logic.
module pri_onehot_unrelated (
  input  wire [15:0] a,
  input  wire [15:0] b,
  input  wire        s,
  output wire [15:0] y
);
  assign y = s ? a : b;
endmodule
