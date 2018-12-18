

module TopModule(
    input logic clk,
    input logic rst,
    output logic [21:0] outOther,
    input logic [1:0] sig,
    input logic flip,
    output logic [1:0] sig_out,
    output logic [15:0] passThrough);

  MyInterface #(.WIDTH(4)) MyInterfaceInstance();

  SubModule1 u_SubModule1 (
    .clk(clk),
    .rst(rst),
    .u_MyInterface(MyInterfaceInstance),
    .outOther(outOther),
    .sig (sig)
  );

  assign sig_out = MyInterfaceInstance.mysig_out;


  assign MyInterfaceInstance.setting = flip;

  assign passThrough = MyInterfaceInstance.passThrough;

endmodule

interface MyInterface #(
  parameter WIDTH = 3)(
  );

  logic setting;
  logic [WIDTH-1:0] other_setting;

  logic [1:0] mysig_out;

  logic [15:0] passThrough;

    modport submodule1 (
        input  setting,
        output other_setting,
        output mysig_out,
        output passThrough
    );

    modport submodule2 (
        input  setting,
        output other_setting,
        input  mysig_out,
        output passThrough
    );

endinterface


module SubModule1(
    input logic clk,
    input logic rst,
    MyInterface.submodule1 u_MyInterface,
    input logic [1:0] sig,
    output logic [21:0] outOther

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
    .u_MyInterfaceInSub3(MyInterfaceInstanceInSub)
  );

    assign outOther = MyInterfaceInstanceInSub.other_setting;

    assign MyInterfaceInstanceInSub.setting = 0;
    assign MyInterfaceInstanceInSub.mysig_out = sig;

endmodule

module SubModule2(

    input logic clk,
    input logic rst,
    MyInterface.submodule2 u_MyInterfaceInSub2,
    MyInterface.submodule2 u_MyInterfaceInSub3

  );

   always_comb begin
      if (u_MyInterfaceInSub3.mysig_out == 2'b00)
        u_MyInterfaceInSub3.other_setting[21:0] = 1000;
      else if (u_MyInterfaceInSub3.mysig_out == 2'b01)
        u_MyInterfaceInSub3.other_setting[21:0] = 2000;
      else if (u_MyInterfaceInSub3.mysig_out == 2'b10)
        u_MyInterfaceInSub3.other_setting[21:0] = 3000;
      else
        u_MyInterfaceInSub3.other_setting[21:0] = 4000;
   end

    assign u_MyInterfaceInSub2.passThrough[7:0] = 124;
    assign u_MyInterfaceInSub2.passThrough[15:8] = 200;

endmodule
