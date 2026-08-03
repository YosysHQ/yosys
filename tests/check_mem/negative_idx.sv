module top;
  (* nomem2reg *)
  logic [1:0] a3 [-2:-1][-1:1] = '{'{0, 1, 2}, '{1, 0, 3}};

  always_comb begin
    assert(a3[-2][-1] == 0);
    assert(a3[-2][0] == 1);
    assert(a3[-2][1] == 2);
    assert(a3[-1][-1] == 1);
    assert(a3[-1][0] == 0);
    assert(a3[-1][1] == 3);
  end
endmodule
