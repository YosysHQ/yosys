module top(
    output logic [5:0] out
);
initial begin
    out = '0;
    case ($bits (out)) 6:
    case ($size (out)) 6:
    case ($high (out)) 5:
    case ($low  (out)) 0:
    case ($left (out)) 5:
    case ($right(out)) 0:
    case (6) $bits (out):
    case (6) $size (out):
    case (5) $high (out):
    case (0) $low  (out):
    case (5) $left (out):
    case (0) $right(out):
        out = '1;
    endcase
    endcase
    endcase
    endcase
    endcase
    endcase
    endcase
    endcase
    endcase
    endcase
    endcase
    endcase
end
endmodule
