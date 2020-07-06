
module MyMem #(
  parameter AddrWidth = 4,
  parameter DataWidth = 4) (
  (* gentb_constant = 1 *)
  input                  Reset_n_i,
  input                  Clk_i,
  input  [AddrWidth-1:0] Addr_i,
  input  [DataWidth-1:0] Data_i,
  output reg [DataWidth-1:0] Data_o,
  input                  WR_i);

  localparam Size = 2**AddrWidth;

  (* mem2reg *)
  reg [DataWidth-1:0] Mem[Size-1:0];

  integer i;

  always @(negedge Reset_n_i or posedge Clk_i)
  begin
    if (!Reset_n_i)
    begin
      Data_o <= 'bx;
      for (i=0; i<Size; i=i+1)
      begin
        Mem[i] <= 0;
      end
    end
    else
    begin
      Data_o <= Mem[Addr_i];
      if (WR_i)
      begin
        Mem[Addr_i] <= Data_i;
      end
    end
  end

endmodule

