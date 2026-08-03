module top (
  input logic clk,
  input logic [1:0][5:0] in_data,
  output logic [1:0][5:0] out_data
);
  (* nomem2reg *)
  logic my_array [1:0][5:0];

  always_ff @(posedge clk) begin
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j <= 5; j++) begin
        my_array[i][j] <= in_data[i][j];
      end
    end
  end

  always_comb begin
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j <= 5; j++) begin
        out_data[i][j] = my_array[i][j];
      end
    end
  end
endmodule
