module top(
    output logic [5:0] out
);
initial begin
    out = '0;
    case (1'b1 << 1)
        2'b10: out = '1;
        default: out = '0;
    endcase
end
endmodule
