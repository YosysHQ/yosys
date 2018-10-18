

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


  assign MyInterfaceInstance.setting = 1;
//  assign MyInterfaceInstance.other_setting[2:0] = 3'b101;

endmodule

interface MyInterface #(
  parameter WIDTH = 3)(
  );

  logic setting;
  logic [WIDTH-1:0] other_setting;

  logic [1:0] mysig_out;

    modport submodule1 (
        input  setting,
        output other_setting,
        output mysig_out
    );

    modport submodule2 (
        input  setting,
        output other_setting,
        input  mysig_out
    );

endinterface


module SubModule1(
    input logic clk,
    input logic rst,
    MyInterface.submodule1 u_MyInterface,
    input logic [1:0] sig

  );

  always_ff @(posedge clk or posedge rst)
    if(rst)
      u_MyInterface.mysig_out <= 0;
    else begin
      if(u_MyInterface.setting)
        u_MyInterface.mysig_out <= sig;
      else
        u_MyInterface.mysig_out <= ~sig;
    end

  MyInterface #(.WIDTH(22)) MyInterfaceInstanceInSub();

  SubModule2 u_SubModule2 (
    .clk(clk),
    .rst(rst),
    .u_MyInterfaceInSub2(u_MyInterface),
    .sig (sig)
  );

endmodule

module SubModule2(

    input logic clk,
    input logic rst,
    MyInterface.submodule2 u_MyInterfaceInSub2,
    input logic [1:0] sig

  );

   assign u_MyInterfaceInSub2.other_setting[2:0] = 9;

endmodule
