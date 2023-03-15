typedef enum {
    WA, WB, WC, WD
} wide_state_t;

typedef enum logic [1:0] {
    A = 3, B = 0, C, D
} state_t;

module top(input clk, output z);

    wide_state_t wide_state = WA;

    always @(posedge clk) begin
        case (wide_state)
            WA: wide_state <= WB;
            WB: wide_state <= WC;
            WC: wide_state <= WD;
            default: wide_state <= WA;
        endcase
    end

    (* some_attribute = shortint'(42) *)
    (* another_attribute = -1 *)
    state_t state = A;

    always @(posedge clk) begin
        case (state)
            A: state <= B;
            B: state <= C;
            C: state <= D;
            default: state <= A;
        endcase
    end

    assign z = (wide_state == WB) ^ (state == B);

endmodule
