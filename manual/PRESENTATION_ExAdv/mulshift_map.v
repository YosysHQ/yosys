module MYMUL(A, B, Y);
    parameter WIDTH = 1;
    input [WIDTH-1:0] A, B;
    output reg [WIDTH-1:0] Y;

    parameter _TECHMAP_CONSTVAL_A_ = WIDTH'bx;
    parameter _TECHMAP_CONSTVAL_B_ = WIDTH'bx;

    reg _TECHMAP_FAIL_;
    wire [1023:0] _TECHMAP_DO_ = "proc; clean";

    integer i;
    always @* begin
    	_TECHMAP_FAIL_ <= 1;
        for (i = 0; i < WIDTH; i=i+1) begin
            if (_TECHMAP_CONSTVAL_A_ === WIDTH'd1 << i) begin
	        _TECHMAP_FAIL_ <= 0;
                Y <= B << i;
	    end
            if (_TECHMAP_CONSTVAL_B_ === WIDTH'd1 << i) begin
	        _TECHMAP_FAIL_ <= 0;
                Y <= A << i;
	    end
	end
    end
endmodule
