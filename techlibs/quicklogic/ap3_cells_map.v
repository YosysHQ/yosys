
module \$__RAM (RADDR,RRLSEL,REN,RMODE,
	    WADDR,WDATA,WEN,WMODE,
	    FMODE,FFLUSH,RCLK,WCLK,RDATA,
	    FFLAGS,FIFO_DEPTH,ENDIAN,POWERDN,PROTECT,
	    UPAE,UPAF,SBOG);

    input [10:0] RADDR,WADDR;
    input [1:0] 	RRLSEL,RMODE,WMODE;
    input 	REN,WEN,FFLUSH,RCLK,WCLK;
    input [31:0] WDATA;
    input [1:0] 	SBOG, ENDIAN, UPAF, UPAE;
    output [31:0] RDATA;
    output [3:0]  FFLAGS;
    input [2:0] 	 FIFO_DEPTH;
    input 	 FMODE, POWERDN, PROTECT;
   
    RAM _TECHMAP_REPLACE_ (
                .RADDR(RADDR),
                .RRLSEL(RRLSEL),
                .REN(REN),
                .RMODE(RMODE),
                .WADDR(WADDR),
                .WDATA(WDATA),
                .WEN(WEN),
                .WMODE(WMODE),
                .FMODE(FMODE),
                .FFLUSH(FFLUSH),
                .RCLK(RCLK),
                .WCLK(WCLK),
                .RDATA(RDATA),
                .FFLAGS(FFLAGS),
                .FIFO_DEPTH(FIFO_DEPTH),
                .ENDIAN(ENDIAN),
                .POWERDN(POWERDN),
                .PROTECT(PROTECT),
                .UPAE(UPAE),
                .UPAF(UPAF),
                .SBOG(SBOG));

endmodule

module \$__DSP (MODE_SEL,COEF_DATA,OPER_DATA,OUT_SEL,ENABLE,CLR,RND,SAT,CLOCK,MAC_OUT,CSEL,OSEL,SBOG);

    input [1:0] MODE_SEL,OUT_SEL;
    input [1:0] CSEL;
    input [1:0] OSEL;
    input [31:0] COEF_DATA,OPER_DATA;
    input ENABLE,CLR,RND,SAT,CLOCK;
    input [1:0]SBOG;
    output [63:0] MAC_OUT;

    DSP _TECHMAP_REPLACE_ (
                .MODE_SEL(MODE_SEL),
                .COEF_DATA(COEF_DATA),
                .OPER_DATA(OPER_DATA),
                .OUT_SEL(OUT_SEL),
                .ENABLE(ENABLE),
                .CLR(CLR),
                .RND(RND),
                .SAT(SAT),
                .CLOCK(CLOCK),
                .MAC_OUT(MAC_OUT),
                .CSEL(CSEL),
                .OSEL(OSEL),
                .SBOG(SBOG));
                
endmodule