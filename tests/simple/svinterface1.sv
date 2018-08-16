

module TopModule(
    input logic clk,
    input logic rst,
    input logic [1:0] sig,
    output logic [1:0] sig_out);

  MyInterface #(.WIDTH(4)) MyInterfaceInstance();

  SubModule1 u_SubModule1 (
    .clk(clk),
    .rst(rst),
    .u_MyInterface(MyInterfaceInstance),
    .sig (sig)
  );

  assign sig_out = MyInterfaceInstance.mysig_out;


  assign u_MyInterfaceInstance.setting = 1;

endmodule

interface MyInterface #(
  parameter WIDTH = 3)(
  );

  logic [1:0] setting;
  logic [WIDTH-1:0] other_setting;

  logic [1:0] mysig_out;

endinterface


module SubModule1(
    input logic clk,
    input logic rst,
    MyInterface u_MyInterface,
    input logic [1:0] sig

  );

  always_ff @(posedge clk or posedge rst)
    if(rst)
      u_MyInterface.mysig_out <= 0;
    else begin
      if(u_MyInterface.setting[0])
        u_MyInterface.mysig_out <= sig;
      else
        u_MyInterface.mysig_out <= ~sig;
    end


endmodule
    
