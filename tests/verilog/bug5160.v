// Regression test for bug mentioned in #5160:
// https://github.com/YosysHQ/yosys/pull/5160#issuecomment-2983643084
module top;
    initial $display( "\\" );
endmodule
