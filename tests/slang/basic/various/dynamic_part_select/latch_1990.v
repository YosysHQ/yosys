module latch_1990 #(
        parameter BUG = 1
) (
	(* nowrshmsk = !BUG *)
        output reg [1:0] x
);
        wire z = 0;
        integer i;
        always @*
                for (i = 0; i < 2; i=i+1)
                        x[z^i] = z^i;
endmodule
