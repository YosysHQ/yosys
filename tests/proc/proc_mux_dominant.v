// Test cases for proc_mux dominant-value optimization.
//
// When a full_case switch has a majority of arms assigning the same value to a
// signal bit, proc_mux uses that dominant value as the starting point instead
// of Sx.  Arms that produce the dominant value are then skipped (the mux
// condition evaluates to "when == else"), avoiding spurious $eq/$mux cells.

// dominant_explicit: 3 of 4 arms assign the same constants (dominant values).
// Expected after proc: one $mux per output word, one $logic_not for the
// selector — zero $eq cells, zero $pmux cells.
module dominant_explicit(input [1:0] s, output reg [2:0] y, output reg [1:0] z);
  always @* begin
    y = 3'b001;
    z = 2'b00;
    case (s)
      2'b00: begin y = 3'b110; z = 2'b11; end  // only arm that differs
      2'b01: begin y = 3'b001; z = 2'b00; end  // explicit dominant
      2'b10: begin y = 3'b001; z = 2'b00; end  // explicit dominant
      2'b11: begin y = 3'b001; z = 2'b00; end  // explicit dominant
    endcase
  end
endmodule

// dominant_wire: dominant value is an input wire (not a constant).
// Expected after proc: 1 $logic_not + 1 $mux, no $eq/$pmux.
module dominant_wire(input [1:0] s, input [2:0] a, output reg [2:0] y);
  always @* begin
    y = a;
    case (s)
      2'b00: y = 3'b110;  // only arm that differs
      2'b01: y = a;       // explicit dominant
      2'b10: y = a;       // explicit dominant
      2'b11: y = a;       // explicit dominant
    endcase
  end
endmodule

// no_dominant: all four arms assign distinct values — no majority.
// The optimization must NOT fire; behavior must be unchanged.
// Expected after proc: $eq cells for each non-zero compare arm, $pmux.
module no_dominant(input [1:0] s, input [2:0] a, b, c, d, output reg [2:0] y);
  always @* begin
    case (s)
      2'b00: y = a;
      2'b01: y = b;
      2'b10: y = c;
      2'b11: y = d;
    endcase
  end
endmodule
