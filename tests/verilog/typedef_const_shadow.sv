module top;
    localparam W = 5;
    typedef logic [W-1:0] T;
    T x; // width 5
    if (1) begin : blk
        localparam W = 10;
        typedef T U;
        typedef logic [W-1:0] V;
        U y; // width 5
        V z; // width 10
    end
endmodule
