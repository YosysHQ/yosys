(* techmap_celltype = "$reduce_or" *)
module my_opt_reduce_or(...);
    parameter A_SIGNED = 0;
    parameter A_WIDTH = 1;
    parameter Y_WIDTH = 1;

    input [A_WIDTH-1:0] A;
    output reg [Y_WIDTH-1:0] Y;

    parameter _TECHMAP_CONSTMSK_A_ = 0;
    parameter _TECHMAP_CONSTVAL_A_ = 0;

    wire _TECHMAP_FAIL_ = count_nonconst_bits() == A_WIDTH;
    wire [1024:0] _TECHMAP_DO_ = "proc;;";

    function integer count_nonconst_bits;
        integer i;
        begin
            count_nonconst_bits = 0;
            for (i = 0; i < A_WIDTH; i=i+1)
                if (!_TECHMAP_CONSTMSK_A_[i])
                    count_nonconst_bits = count_nonconst_bits+1;
        end
    endfunction

    function has_const_one;
        integer i;
        begin
            has_const_one = 0;
            for (i = 0; i < A_WIDTH; i=i+1)
                if (_TECHMAP_CONSTMSK_A_[i] && _TECHMAP_CONSTVAL_A_[i] === 1'b1)
                    has_const_one = 1;
        end
    endfunction

    integer i;
    reg [count_nonconst_bits()-1:0] tmp;

    always @* begin
        if (has_const_one()) begin
            Y = 1;
        end else begin
            for (i = 0; i < A_WIDTH; i=i+1)
                if (!_TECHMAP_CONSTMSK_A_[i])
                    tmp = {A[i], tmp[count_nonconst_bits()-1:1]};
            Y = |tmp;
        end
    end
endmodule
