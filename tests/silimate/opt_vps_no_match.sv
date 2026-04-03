// Simple mux-based register -- no VPS pattern, opt_vps should not fire.
module opt_vps_no_match (
    input  logic        clk,
    input  logic        sel,
    input  logic [7:0]  a, b,
    output logic [7:0]  q
);
    logic [7:0] reg_data;
    always_ff @(posedge clk)
        reg_data <= sel ? a : b;
    assign q = reg_data;
endmodule
