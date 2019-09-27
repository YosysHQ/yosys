module retime_test(input clk, input [7:0] a, output z);
    reg [7:0] ff = 8'hF5;
    always @(posedge clk)
        ff <= {ff[6:0], ^a};
    assign z = ff[7];
endmodule
