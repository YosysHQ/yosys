/*
Example from: https://www.latticesemi.com/-/media/LatticeSemi/Documents/UserManuals/EI/iCEcube201701UserGuide.ashx?document_id=52071 [p. 77].
*/
module top(clk,a,b,c,set);
parameter A_WIDTH = 6 /*4*/;
parameter B_WIDTH = 6 /*3*/;
input set;
input clk;
input signed [(A_WIDTH - 1):0] a;
input signed [(B_WIDTH - 1):0] b;
output signed [(A_WIDTH + B_WIDTH - 1):0] c;
reg [(A_WIDTH + B_WIDTH - 1):0] reg_tmp_c;
assign c = reg_tmp_c;
always @(posedge clk)
begin
    if(set)
    begin
        reg_tmp_c <= 0;
    end
    else
    begin
        reg_tmp_c <= a * b + c;
    end
end
endmodule

module top2(clk,a,b,c,hold);
parameter A_WIDTH = 6 /*4*/;
parameter B_WIDTH = 6 /*3*/;
input hold;
input clk;
input signed [(A_WIDTH - 1):0] a;
input signed [(B_WIDTH - 1):0] b;
output signed [(A_WIDTH + B_WIDTH - 1):0] c;
reg signed [A_WIDTH-1:0] reg_a;
reg signed [B_WIDTH-1:0] reg_b;
reg [(A_WIDTH + B_WIDTH - 1):0] reg_tmp_c;
assign c = reg_tmp_c;
always @(posedge clk)
begin
    if (!hold) begin
        reg_a <= a;
        reg_b <= b;
        reg_tmp_c <= reg_a * reg_b + c;
    end
end
endmodule
