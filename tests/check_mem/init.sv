module top (
  input logic clk,
  input logic idx,
  output logic [2:0] out_data
);
  (* nomem2reg *)
  logic my_array [3:2][2:0] = '{'{0, 1, 1}, '{1, 0, 1}};

  always_comb begin
    for (int i=0; i < 3; i++) begin
        out_data[i] = my_array[{1'b1, idx}][i];
    end
  end

endmodule
