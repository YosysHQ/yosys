
module TopModule(
    input logic clk,
    input logic rst,
    input logic [1:0] sig,
    input logic flip,
    output logic [15:0] passThrough,
    output logic [21:0] outOther,
    output logic [1:0] sig_out);


    logic MyInterfaceInstance_setting;
    logic [3:0] MyInterfaceInstance_other_setting;
    logic [1:0] MyInterfaceInstance_mysig_out;

  SubModule1 u_SubModule1 (
    .clk(clk),
    .rst(rst),
    .u_MyInterface_setting(MyInterfaceInstance_setting),
    .u_MyInterface_mysig_out(MyInterfaceInstance_mysig_out),
    .u_MyInterface_other_setting(MyInterfaceInstance_other_setting),
    .outOther(outOther),
    .passThrough (passThrough),
    .sig (sig)
  );

  assign sig_out = MyInterfaceInstance_mysig_out;


  assign MyInterfaceInstance_setting = flip;

endmodule


module SubModule1(
    input logic clk,
    input logic rst,
    input logic u_MyInterface_setting,
    output logic [3:0] u_MyInterface_other_setting,
    output logic [1:0] u_MyInterface_mysig_out,
    output logic [21:0] outOther,
    input logic [1:0] sig,
    output logic [15:0] passThrough
  );

  always @(posedge clk or posedge rst)
    if(rst)
      u_MyInterface_mysig_out <= 0;
    else begin
      if(u_MyInterface_setting)
        u_MyInterface_mysig_out <= sig;
      else
        u_MyInterface_mysig_out <= ~sig;
    end

    logic MyInterfaceInstanceInSub_setting;
    logic [21:0] MyInterfaceInstanceInSub_other_setting;
    logic [1:0] MyInterfaceInstanceInSub_mysig_out;


  SubModule2 u_SubModule2 (
    .clk(clk),
    .rst(rst),
    .u_MyInterfaceInSub2_setting(u_MyInterface_setting),
    .u_MyInterfaceInSub2_mysig_out(u_MyInterface_mysig_out),
    .u_MyInterfaceInSub2_other_setting(u_MyInterface_other_setting),
    .u_MyInterfaceInSub3_setting(MyInterfaceInstanceInSub_setting),
    .u_MyInterfaceInSub3_mysig_out(MyInterfaceInstanceInSub_mysig_out),
    .u_MyInterfaceInSub3_other_setting(MyInterfaceInstanceInSub_other_setting),
    .passThrough (passThrough)
  );
    assign outOther = MyInterfaceInstanceInSub_other_setting;

    assign MyInterfaceInstanceInSub_setting = 0;
    assign MyInterfaceInstanceInSub_mysig_out = sig;

endmodule

module SubModule2(

    input logic clk,
    input logic rst,
    input logic u_MyInterfaceInSub2_setting,
    output logic [3:0] u_MyInterfaceInSub2_other_setting,
    input  logic [1:0] u_MyInterfaceInSub2_mysig_out,
    input logic u_MyInterfaceInSub3_setting,
    output logic [21:0] u_MyInterfaceInSub3_other_setting,
    input  logic [1:0] u_MyInterfaceInSub3_mysig_out,
    output logic [15:0] passThrough

  );

    always @(u_MyInterfaceInSub3_mysig_out) begin
      if (u_MyInterfaceInSub3_mysig_out == 2'b00)
        u_MyInterfaceInSub3_other_setting[21:0] = 1000;
      else if (u_MyInterfaceInSub3_mysig_out == 2'b01)
        u_MyInterfaceInSub3_other_setting[21:0] = 2000;
      else if (u_MyInterfaceInSub3_mysig_out == 2'b10)
        u_MyInterfaceInSub3_other_setting[21:0] = 3000;
      else
        u_MyInterfaceInSub3_other_setting[21:0] = 4000;
    end

    assign passThrough[7:0] = 124;
    assign passThrough[15:8] = 200;

endmodule
