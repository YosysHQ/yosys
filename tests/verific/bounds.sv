typedef enum {IDLE, RUN, STOP} state_t;

typedef struct {
    logic [7:0] field1;
    int field2;
} my_struct_t;

// Submodule to handle the interface ports
module submodule (
    my_ifc i_ifc,
    my_ifc o_ifc
);
    // Connect the interface signals
    assign o_ifc.data = i_ifc.data;
endmodule

module test (
    input i_a,
    output o_a,
    input [0:0] i_b,
    output [0:0] o_b,
    input [3:0] i_c,
    output [3:0] o_c,
    input logic i_d,
    output logic o_d,
    input bit [7:0] i_e,
    output bit [7:0] o_e,
    input int i_f,
    output int o_f,
    input state_t i_h,
    output state_t o_h,
    input my_struct_t i_i,
    output my_struct_t o_i
);

    assign o_a = i_a;
    assign o_b = i_b;
    assign o_c = i_c;
    assign o_d = i_d;
    assign o_e = i_e;
    assign o_f = i_f;
    assign o_h = i_h;
    assign o_i = i_i;

endmodule
