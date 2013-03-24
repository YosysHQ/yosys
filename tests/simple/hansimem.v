
module MyMem #(
  parameter AddrWidth = 4,
  parameter DataWidth = 4) (
  (* gentb_constant = 1 *)
  input                  Reset_n_i,
  input                  Clk_i,
  input  [AddrWidth-1:0] Addr_i,
  input  [DataWidth-1:0] Data_i,
  output [DataWidth-1:0] Data_o,
  input                  WR_i);

  reg Data_o;

  localparam Size = 2**AddrWidth;

  (* mem2reg *)
  reg [DataWidth-1:0] Mem[Size-1:0];

  integer i;

  always @(negedge Reset_n_i or posedge Clk_i)
  begin
    //$display("Data1 = %b, Data11 = %b, Data12 = %b, Data2 = %b, Data21 = %b, Data22 = %b",Data1_i,Data11,Data12,Data2_i,Data21,Data22);
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

