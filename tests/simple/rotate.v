
// test case taken from amber23 Verilog code
module a23_barrel_shift_fpga_rotate(i_in, direction, shift_amount, rot_prod);

input  [31:0] i_in;
input         direction;
input  [4:0]  shift_amount;
output [31:0] rot_prod;

// Generic rotate. Theoretical cost: 32x5 4-to-1 LUTs.
// Practically a bit higher due to high fanout of "direction".
generate
genvar i, j;
        for (i = 0; i < 5; i = i + 1)
        begin : netgen
                wire [31:0] in;
                reg [31:0] out;
                for (j = 0; j < 32; j = j + 1)
                begin : net
                        always @*
                                out[j] = in[j] & (~shift_amount[i] ^ direction) |
                                         in[wrap(j, i)] & (shift_amount[i] ^ direction);
                end
        end

        // Order is reverted with respect to volatile shift_amount[0]
        assign netgen[4].in = i_in;
        for (i = 1; i < 5; i = i + 1)
        begin : router
                assign netgen[i-1].in = netgen[i].out;
        end
endgenerate

// Aliasing
assign rot_prod = netgen[0].out;

function [4:0] wrap;
input integer pos;
input integer level;
integer out;
begin
        out = pos - (1 << level);
        wrap = out[4:0];
end
endfunction

endmodule

