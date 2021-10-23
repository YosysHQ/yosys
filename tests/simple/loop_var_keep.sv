module top (
    input logic inp,
    output logic [4:0] out
);
    always @* begin
        out = 0;
        if (inp) begin
            int i;
            for (i = 0; i < 5; i++)
                out[i] = 1'b1;
            out[i - 1] = 1'b0;
        end
    end
endmodule
