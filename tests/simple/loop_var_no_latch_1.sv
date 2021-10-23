module top (
    input logic inp,
    output logic [4:0] out
);
    always_comb begin
        out = 0;
        if (inp) begin
            int i;
            for (i = 0; i < 5; i++)
                out[i] = 1'b1;
        end
    end
endmodule
