module top (
  input logic clk,
  input logic [3:1][2:0] in_data,
  output logic [3:1][2:0] out_data
);
  (* nomem2reg *)
  logic [2:0] my_array [3:1];

  always_ff @(posedge clk) begin
    for (int i = 1; i <= 3; i++) begin
      my_array[i] <= in_data[i];
    end
  end

  always_comb begin
    for (int i = 1; i <= 3; i++) begin
      out_data[i] = my_array[i];
    end
  end

endmodule
