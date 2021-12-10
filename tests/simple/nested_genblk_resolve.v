`default_nettype none
module nested_genblk_resolve_top;
    generate
        if (1) begin
            wire x;
            genvar i;
            for (i = 0; i < 1; i = i + 1) begin
                if (1) begin
                    assign x = 1;
                end
            end
        end
    endgenerate
endmodule
