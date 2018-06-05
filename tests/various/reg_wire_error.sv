module sub_mod(input i_in, output o_out);
assign o_out = i_in;
endmodule

module test(i_clk, i, i_reg, o_reg, o_wire, o_mr, o_mw, o_ml);
input i_clk;
input i;
input i_reg;
output o_reg;
output o_wire;
output o_mr, o_mw, o_ml;

// Enable this to see how it doesn't fail on yosys although it should
//reg o_wire;
// Enable this instead of the above to see how logic can be mapped to a wire
logic o_wire;
// Enable this to see how it doesn't fail on yosys although it should
//reg i_reg;
// Disable this to see how it doesn't fail on yosys although it should
//reg o_reg;

logic l_reg;

// Enable this to tst if logic-turne-reg will catch assignments even if done before it turned into a reg
assign l_reg = !o_reg;
initial o_reg = 1'b0;
always @(posedge i_clk)
begin
  o_reg <= !o_reg;
  l_reg <= !o_reg;
end

assign o_wire = !o_reg;
// Uncomment this to see how a logic already turned intoa reg can be freely assigned on yosys
assign l_reg = !o_reg;

sub_mod sm_inst (
  .i_in(1'b1),
  .o_out(o_reg)
);

wire   mw1[0:1];
wire   mw2[0:1];
wire   mw3[0:1];
reg    mr1[0:1];
reg    mr2[0:1];
reg    mr3[0:1];
logic  ml1[0:1];
logic  ml2[0:1];
logic  ml3[0:1];

assign o_mw = mw1[i];
assign o_mr = mr1[i];
assign o_ml = ml1[i];

assign mw1[1] = 1'b1;
//assign mr1[1] = 1'b1;
assign ml1[1] = 1'b1;
always @(posedge i_clk)
begin
  mr2[0] = 1'b0;
  mw2[0] = 1'b0;
  ml2[0] = 1'b0;
end

always @(posedge i_clk)
begin
  mr3[0] <= 1'b0;
  mw3[0] <= 1'b0;
  ml3[0] <= 1'b0;
end

endmodule

