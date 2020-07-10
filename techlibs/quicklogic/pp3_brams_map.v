module \$__QUICKLOGIC_RAMB16K (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 36;
	parameter CFG_ENABLE_B = 4;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [16383:0] INIT = 16384'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;
	input A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input [CFG_ENABLE_B-1:0] B1EN;
	
	assign VCC = 1'b1;
	assign GND = 1'b0;
  
	wire [3:0] DIP, DOP;
	wire [31:0] DI, DO;

	wire [31:0] DOB;
	wire [3:0] DOPB;

	wire[1:0] WS1_0;
	wire[1:0] WS1_1;
	wire[1:0] WS2_0;
	wire[1:0] WS2_1;
  
  	wire[4:0] wen_reg;

	assign wen_reg[4:CFG_ENABLE_B]=0;
	assign wen_reg[CFG_ENABLE_B-1:0]=B1EN;
	
	assign A1DATA = DO;
	assign DI = B1DATA;

    	if(CFG_DBITS <=8)
	begin
             assign WS1_0 = 2'b00;
             assign WS2_0 = 2'b00;
	end
    	else if(CFG_DBITS >8 && CFG_DBITS <=16)
	begin
             assign WS1_0 = 2'b01;
             assign WS2_0 = 2'b01;
	end
    	else if(CFG_DBITS > 16)
	begin
             assign WS1_0 = 2'b10;
             assign WS2_0 = 2'b10;
	end

	generate if (CFG_DBITS <= 16) begin
       	ram8k_2x1_cell_macro #(
		 `include "bram_init_32.vh"
		) _TECHMAP_REPLACE_ (			
		   .A1_0(B1ADDR) ,
		   .A1_1(GND),
		   .A2_0(A1ADDR),
		   .A2_1(GND),
		   .ASYNC_FLUSH_0(GND), 
		   .ASYNC_FLUSH_1(GND), 
		   .ASYNC_FLUSH_S0(GND),
		   .ASYNC_FLUSH_S1(GND),
		   .CLK1_0(CLK2),
		   .CLK1_1(CLK2),
		   .CLK1S_0(!CLKPOL2),
		   .CLK1S_1(!CLKPOL2),
		   .CLK1EN_0(VCC),
		   .CLK1EN_1(VCC),
		   .CLK2_0(CLK3),
		   .CLK2_1(CLK3),
		   .CLK2S_0(!CLKPOL3),
		   .CLK2S_1(!CLKPOL3),
		   .CLK2EN_0(A1EN),
		   .CLK2EN_1(A1EN),
		   .CONCAT_EN_0(VCC),
		   .CONCAT_EN_1(GND),
		   .CS1_0(VCC),
		   .CS1_1(GND),
		   .CS2_0(VCC),
		   .CS2_1(GND),
		   .DIR_0(GND),
		   .DIR_1(GND),
		   .FIFO_EN_0(GND),
		   .FIFO_EN_1(GND),
		   .P1_0(GND), 
		   .P1_1(GND), 
		   .P2_0(GND), 
		   .P2_1(GND), 
		   .PIPELINE_RD_0(GND),
		   .PIPELINE_RD_1(GND),
		   .SYNC_FIFO_0(GND),
		   .SYNC_FIFO_1(GND),
		   .WD_1(GND),
		   .WD_0({GND, DI[15: 8], GND, DI[ 7: 0]}),
		   .WIDTH_SELECT1_0(WS1_0),
		   .WIDTH_SELECT1_1(GND),
		   .WIDTH_SELECT2_0(WS2_0),
		   .WIDTH_SELECT2_1(GND),
                   .WEN1_0(wen_reg[1:0]), 
		   .WEN1_1(wen_reg[3:2]),
		   .Almost_Empty_0(),
		   .Almost_Empty_1(),
		   .Almost_Full_0(),
		   .Almost_Full_1(),
		   .POP_FLAG_0(),
		   .POP_FLAG_1(),
		   .PUSH_FLAG_0(),
		   .PUSH_FLAG_1(),
		   .RD_0({DOP[1], DO[15: 8], DOP[0], DO[ 7: 0]}),
		   .RD_1(),
		   .TEST1A(GND),
		   .TEST1B(GND),
		   .RMA(4'd0),
		   .RMB(4'd0),
		   .RMEA(GND),
		   .RMEB(GND)
		   );
         end else  if (CFG_DBITS <= 32) begin
       	 ram8k_2x1_cell_macro #(
		  `include "bram_init_32.vh"
		   ) _TECHMAP_REPLACE_ (			
		   .A1_0(B1ADDR) ,
		   .A1_1(GND),
		   .A2_0(A1ADDR),
		   .A2_1(GND),
		   .ASYNC_FLUSH_0(GND), 
		   .ASYNC_FLUSH_1(GND), 
		   .ASYNC_FLUSH_S0(GND),
		   .ASYNC_FLUSH_S1(GND),
		   .CLK1_0(CLK2),
		   .CLK1_1(CLK2),
		   .CLK1S_0(!CLKPOL2),
		   .CLK1S_1(!CLKPOL2),
		   .CLK1EN_0(VCC),
		   .CLK1EN_1(VCC),
		   .CLK2_0(CLK3),
		   .CLK2_1(CLK3),
		   .CLK2S_0(!CLKPOL3),
		   .CLK2S_1(!CLKPOL3),
		   .CLK2EN_0(A1EN),
		   .CLK2EN_1(A1EN),
		   .CONCAT_EN_0(VCC),
		   .CONCAT_EN_1(GND),
		   .CS1_0(VCC),
		   .CS1_1(GND),
		   .CS2_0(VCC),
		   .CS2_1(GND),
		   .DIR_0(GND),
		   .DIR_1(GND),
		   .FIFO_EN_0(GND),
		   .FIFO_EN_1(GND),
		   .P1_0(GND), 
		   .P1_1(GND), 
		   .P2_0(GND), 
		   .P2_1(GND), 
		   .PIPELINE_RD_0(GND),
		   .PIPELINE_RD_1(GND),
		   .SYNC_FIFO_0(GND),
		   .SYNC_FIFO_1(GND),
		   .WD_1({GND, DI[31:24], GND, DI[23:16]}),
		   .WD_0({GND, DI[15: 8], GND, DI[ 7: 0]}),
		   .WIDTH_SELECT1_0(WS1_0),
		   .WIDTH_SELECT1_1(GND),
		   .WIDTH_SELECT2_0(WS2_0),
		   .WIDTH_SELECT2_1(GND),
                   .WEN1_0(wen_reg[1:0]), 
		   .WEN1_1(wen_reg[3:2]),
		   .Almost_Empty_0(),
		   .Almost_Empty_1(),
		   .Almost_Full_0(),
		   .Almost_Full_1(),
		   .POP_FLAG_0(),
		   .POP_FLAG_1(),
		   .PUSH_FLAG_0(),
		   .PUSH_FLAG_1(),
		   .RD_0({DOP[1], DO[15: 8], DOP[0], DO[ 7: 0]}),
		   .RD_1({DOP[3], DO[31:24], DOP[2], DO[23:16]}),
		   .TEST1A(GND),
		   .TEST1B(GND),
		   .RMA(4'd0),
		   .RMB(4'd0),
		   .RMEA(GND),
		   .RMEB(GND)
		   );
         end else begin
                wire TECHMAP_FAIL = 1'b1;
        end endgenerate  
endmodule

// ------------------------------------------------------------------------

module \$__QUICKLOGIC_RAMB8K (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 18;
	parameter CFG_ENABLE_B = 2;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [8191:0] INIT = 8192'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;
	input A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input [CFG_ENABLE_B-1:0] B1EN;

	wire [10:0] A1ADDR_11;
	wire [10:0] B1ADDR_11;

	wire [1:0] DIP, DOP;
	wire [15:0] DI, DO;

	wire [15:0] DOBDO;
	wire [1:0] DOPBDOP;
	
	wire[1:0] WS1_0;
	wire[1:0] WS1_1;
	wire[1:0] WS2_0;
	wire[1:0] WS2_1;
  
        wire[2:0] wen_reg;

        assign wen_reg[2:CFG_ENABLE_B]=0;
        assign wen_reg[CFG_ENABLE_B-1:0]=B1EN;

	assign GND = 1'b0;
	assign VCC = 1'b1;

	assign A1DATA = DO;
	assign DI = B1DATA;

        if(CFG_ABITS == 11)
        begin
             assign A1ADDR_11[CFG_ABITS-1:0]=A1ADDR;
             assign B1ADDR_11[CFG_ABITS-1:0]=B1ADDR;
        end
	else
        begin
	     assign A1ADDR_11[10:CFG_ABITS]=0;
             assign A1ADDR_11[CFG_ABITS-1:0]=A1ADDR;
	     assign B1ADDR_11[10:CFG_ABITS]=0;
             assign B1ADDR_11[CFG_ABITS-1:0]=B1ADDR;
        end

        if(CFG_DBITS <=9)
	begin
             assign WS1_0 = 2'b00;
             assign WS2_0 = 2'b00;
	end
    	else if(CFG_DBITS >9 && CFG_DBITS <=18)
	begin
             assign WS1_0 = 2'b01;
             assign WS2_0 = 2'b01;
	end
    	else if(CFG_DBITS > 18)
	begin
             assign WS1_0 = 2'b10;
             assign WS2_0 = 2'b10;
	end

	ram8k_2x1_cell_macro #(
            `include "bram_init_8_16.vh"
        ) _TECHMAP_REPLACE_ (			
		   .A1_0(B1ADDR_11) ,
		   .A1_1(GND),
		   .A2_0(A1ADDR_11),
		   .A2_1(GND),
		   .ASYNC_FLUSH_0(GND),
		   .ASYNC_FLUSH_1(GND), 
		   .ASYNC_FLUSH_S0(GND),
		   .ASYNC_FLUSH_S1(GND),
		   .CLK1_0(CLK2),
		   .CLK1_1(GND),
		   .CLK1S_0(!CLKPOL2),
		   .CLK1S_1(GND),
		   .CLK1EN_0(VCC),
		   .CLK1EN_1(VCC),
		   .CLK2_0(CLK3),
		   .CLK2_1(GND),
		   .CLK2S_0(!CLKPOL3),
		   .CLK2S_1(GND),
		   .CLK2EN_0(A1EN),
		   .CLK2EN_1(GND),
		   .CONCAT_EN_0(GND),
		   .CONCAT_EN_1(GND),
		   .CS1_0(VCC),
		   .CS1_1(GND),
		   .CS2_0(VCC),
		   .CS2_1(GND),
		   .DIR_0(GND),
		   .DIR_1(GND),
		   .FIFO_EN_0(GND),
		   .FIFO_EN_1(GND),
		   .P1_0(GND), 
		   .P1_1(GND), 
		   .P2_0(GND), 
		   .P2_1(GND), 
		   .PIPELINE_RD_0(GND),
		   .PIPELINE_RD_1(GND),
		   .SYNC_FIFO_0(GND),
		   .SYNC_FIFO_1(GND),
		   .WD_1(GND),
		   .WD_0({GND, DI[15: 8], GND, DI[ 7: 0]}),
		   .WIDTH_SELECT1_0(WS1_0),
		   .WIDTH_SELECT1_1(GND),
		   .WIDTH_SELECT2_0(WS2_0),
		   .WIDTH_SELECT2_1(GND),
		   .WEN1_0(wen_reg[1:0]),
		   .WEN1_1(GND),
		   .Almost_Empty_0(),
		   .Almost_Empty_1(),
		   .Almost_Full_0(),
		   .Almost_Full_1(),
		   .POP_FLAG_0(),
		   .POP_FLAG_1(),
		   .PUSH_FLAG_0(),
		   .PUSH_FLAG_1(),
		   .RD_0({DOP[1], DO[15: 8], DOP[0], DO[ 7: 0]}),
		   .RD_1(),
		   .TEST1A(GND),
		   .TEST1B(GND),
		   .RMA(4'd0),
		   .RMB(4'd0),
		   .RMEA(GND),
		   .RMEB(GND)
		   );
endmodule

module RAM_8K_BLK ( WA,RA,WD,WClk,RClk,WClk_En,RClk_En,WEN,RD);

parameter addr_int 	= 9,
          data_depth_int = 512,
          data_width_int = 18,
          wr_enable_int 	= 2,
          reg_rd_int 	= 0;
			
parameter [8191:0] INIT = 8192'bx;
parameter INIT_FILE="init.mem";	
			
input [addr_int-1:0] WA;
input [addr_int-1:0] RA;
input WClk,RClk;
input WClk_En,RClk_En;
input [wr_enable_int-1:0] WEN;
input [data_width_int-1:0] WD;
output [data_width_int-1:0] RD;

wire VCC,GND;
wire WClk0_Sel,RClk0_Sel;
wire WClk1_Sel,RClk1_Sel;

wire reg_rd0;
wire reg_rd1;
wire [10:0] addr_wr0,addr_rd0,addr_wr1,addr_rd1;

wire [17:0] in_reg0;

wire [2:0] wen_reg0;

wire [15:0] out_reg0;

wire [1:0] out_par0;

wire [1:0] WS1_0,WS2_0; 
wire [1:0] WS_GND;

wire LS,DS,SD,LS_RB1,DS_RB1,SD_RB1;

wire WD0_SEL,RD0_SEL;
wire WD1_SEL,RD1_SEL;

assign VCC = 1'b1;
assign GND = 1'b0;

assign WD0_SEL = 1'b1;
assign RD0_SEL = 1'b1;
assign WD1_SEL = 1'b0;
assign RD1_SEL = 1'b0;

assign WClk0_Sel = 1'b0;
assign RClk0_Sel = 1'b0;

assign WClk1_Sel = 1'b0;
assign RClk1_Sel = 1'b0;

assign LS = 1'b0;
assign DS = 1'b0;
assign SD = 1'b0;
assign LS_RB1 = 1'b0;
assign DS_RB1 = 1'b0;
assign SD_RB1 = 1'b0;

assign reg_rd0 =reg_rd_int;
assign WS_GND = 2'b00;

assign reg_rd1 =1'b0;

assign wen_reg0[2:wr_enable_int]=0;
assign wen_reg0[wr_enable_int-1:0]=WEN;

assign addr_wr1=11'b0000000000;
assign addr_rd1=11'b0000000000;

generate

	if(addr_int == 11)
	begin
	     assign addr_wr0[10:0]=WA;
	     assign addr_rd0[10:0]=RA;
	end
	else
	begin
	     assign addr_wr0[10:addr_int]=0;
	     assign addr_wr0[addr_int-1:0]=WA;
	     assign addr_rd0[10:addr_int]=0;
	     assign addr_rd0[addr_int-1:0]=RA;
	end

  	if (data_width_int == 16) 
	begin
    	     assign in_reg0[data_width_int-1:0] =WD[data_width_int-1:0]; 
        end  
        else if (data_width_int > 8 && data_width_int < 16)
        begin
	     assign in_reg0[15:data_width_int] =0;
             assign in_reg0[data_width_int-1:0] =WD[data_width_int-1:0]; 
        end
  	else if (data_width_int <= 8) 
	begin
	     assign in_reg0[15:data_width_int] =0;
             assign in_reg0[data_width_int-1:0] =WD[data_width_int-1:0]; 
        end

	if(data_width_int <=8)
        begin
	     assign WS1_0 = 2'b00;
	     assign WS2_0 = 2'b00;
    	end
	else if(data_width_int >8 && data_width_int <=16)
  	begin
	     assign WS1_0 = 2'b01;
	     assign WS2_0 = 2'b01;
        end
	else if(data_width_int > 16)
  	begin
	     assign WS1_0 = 2'b10;
	     assign WS2_0 = 2'b10;
        end

endgenerate

	ram8k_2x1_cell_macro # (
                       `include "bram_init_8_16.vh"
                         )
    	_TECHMAP_REPLACE_ (
                       .A1_0(addr_wr0) , 
                       .A1_1(addr_wr1), 
                       .A2_0(addr_rd0), 
                       .A2_1(addr_rd1), 
                       .ASYNC_FLUSH_0(GND), 
                       .ASYNC_FLUSH_1(GND), 
                       .ASYNC_FLUSH_S0(GND),
                       .ASYNC_FLUSH_S1(GND),
                       .CLK1_0(WClk), 
                       .CLK1_1(GND), 
                       .CLK1S_0(WClk0_Sel), 
                       .CLK1S_1(WClk1_Sel),
                       .CLK1EN_0(WClk_En), 
                       .CLK1EN_1(GND), 
                       .CLK2_0(RClk),
                       .CLK2_1(GND), 
                       .CLK2S_0(RClk0_Sel),
                       .CLK2S_1(RClk1_Sel), 
                       .CLK2EN_0(RClk_En), 
                       .CLK2EN_1(GND), 
                       .CONCAT_EN_0(GND),
                       .CONCAT_EN_1(GND), 
                       .CS1_0(WD0_SEL), 
                       .CS1_1(WD1_SEL), 
                       .CS2_0(RD0_SEL), 
                       .CS2_1(RD1_SEL), 
                       .DIR_0(GND),
                       .DIR_1(GND), 
                       .FIFO_EN_0(GND), 
                       .FIFO_EN_1(GND), 
                       .P1_0(GND), 
                       .P1_1(GND), 
                       .P2_0(GND), 
                       .P2_1(GND), 
                       .PIPELINE_RD_0(reg_rd0), 
                       .PIPELINE_RD_1(reg_rd1), 
                       .SYNC_FIFO_0(GND),
                       .SYNC_FIFO_1(GND), 
                       .WD_1({18{GND}}), 
                       .WD_0({1'b0,in_reg0[15:8],1'b0,in_reg0[7:0]}), 
                       .WIDTH_SELECT1_0(WS1_0), 
                       .WIDTH_SELECT1_1(WS_GND), 
                       .WIDTH_SELECT2_0(WS2_0),
                       .WIDTH_SELECT2_1(WS_GND), 
                       .WEN1_0(wen_reg0[1:0]), 
                       .WEN1_1({2{GND}}), 
                       .Almost_Empty_0(),
                       .Almost_Empty_1(), 
                       .Almost_Full_0(), 
                       .Almost_Full_1(),
                       .POP_FLAG_0(), 
                       .POP_FLAG_1(), 
                       .PUSH_FLAG_0(), 
                       .PUSH_FLAG_1(),
                       .RD_0({out_par0[1],out_reg0[15:8],out_par0[0],out_reg0[7:0]}), 
                       .RD_1(),
                       .SD(SD),
                       .SD_RB1(SD_RB1),
                       .LS(LS),
                       .LS_RB1(LS_RB1),
                       .DS(DS),
                       .DS_RB1(DS_RB1),
                       .TEST1A(GND),
                       .TEST1B(GND),
                       .RMA(4'd0),
                       .RMB(4'd0),
                       .RMEA(GND),
		       .RMEB(GND)
	                );
						
         assign RD[data_width_int-1 :0]= out_reg0[data_width_int-1 :0];

endmodule


module RAM_16K_BLK ( WA,RA,WD,WClk,RClk,WClk_En,RClk_En,WEN,RD);

parameter addr_int       = 9,
          data_depth_int = 512,
	  data_width_int = 36,
          wr_enable_int  = 4,
	  reg_rd_int 	 = 0;

parameter [16383:0] INIT = 16384'bx;
parameter INIT_FILE="init.mem";	
			
input [addr_int-1:0] WA;
input [addr_int-1:0] RA;
input WClk,RClk;
input WClk_En,RClk_En;
input [wr_enable_int-1:0] WEN;
input [data_width_int-1:0] WD;
output [data_width_int-1:0] RD;

wire VCC,GND;

wire WClk0_Sel,RClk0_Sel;
wire WClk1_Sel,RClk1_Sel;

wire reg_rd0;
wire reg_rd1;
wire [10:0] addr_wr0,addr_rd0,addr_wr1,addr_rd1;

wire [31:0] in_reg0;

wire [4:0] wen_reg0;

wire [31:0] out_reg0;

wire [3:0] out_par0;

wire [1:0] WS1_0,WS2_0; 
wire [1:0] WS_GND;

wire LS,DS,SD,LS_RB1,DS_RB1,SD_RB1;

wire WD0_SEL,RD0_SEL;
wire WD1_SEL,RD1_SEL;

assign VCC = 1'b1;
assign GND = 1'b0;

assign WD0_SEL = 1'b1;
assign RD0_SEL = 1'b1;
assign WD1_SEL = 1'b1;
assign RD1_SEL = 1'b1;

assign WClk0_Sel = 1'b0;
assign RClk0_Sel = 1'b0;

assign WClk1_Sel = 1'b0;
assign RClk1_Sel = 1'b0;

assign LS = 1'b0;
assign DS = 1'b0;
assign SD = 1'b0;
assign LS_RB1 = 1'b0;
assign DS_RB1 = 1'b0;
assign SD_RB1 = 1'b0;

assign reg_rd0 =reg_rd_int;
assign WS_GND = 2'b00;

assign reg_rd1 = 1'b0;

assign wen_reg0[4:wr_enable_int]=0;
assign wen_reg0[wr_enable_int-1:0]=WEN;

assign addr_wr1=11'b0000000000;
assign addr_rd1=11'b0000000000;

generate

	if(addr_int == 11)
	begin
	     assign addr_wr0[10:0]=WA;
	     assign addr_rd0[10:0]=RA;
	end
	else
	begin
	     assign addr_wr0[10:addr_int]=0;
	     assign addr_wr0[addr_int-1:0]=WA;
	     assign addr_rd0[10:addr_int]=0;
	     assign addr_rd0[addr_int-1:0]=RA;
	end
	
  	if (data_width_int == 32) 
	begin
    	     assign in_reg0[data_width_int-1:0] =WD[data_width_int-1:0]; 
  	end  
  	else if (data_width_int > 8 && data_width_int < 32)
  	begin
	     assign in_reg0[31:data_width_int] =0;
             assign in_reg0[data_width_int-1:0] =WD[data_width_int-1:0]; 
  	end
  	else if (data_width_int <= 8) 
	begin
	     assign in_reg0[31:data_width_int] =0;
    	     assign in_reg0[data_width_int-1:0] =WD[data_width_int-1:0]; 
   	end

	if(data_width_int <=8)
  	begin
	     assign WS1_0 = 2'b00;
	     assign WS2_0 = 2'b00;
  	end
	else if(data_width_int >8 && data_width_int <=16)
  	begin
	     assign WS1_0 = 2'b01;
	     assign WS2_0 = 2'b01;
  	end
	else if(data_width_int > 16)
  	begin
	     assign WS1_0 = 2'b10;
	     assign WS2_0 = 2'b10;
  	end

	if (data_width_int <=16)  begin

    	    ram8k_2x1_cell_macro # (
                        `include "bram_init_32.vh"
                            )
			_TECHMAP_REPLACE_ (
                        .A1_0(addr_wr0) , 
                        .A1_1(addr_wr1), 
                        .A2_0(addr_rd0), 
                        .A2_1(addr_rd1), 
                        .ASYNC_FLUSH_0(GND), 
                        .ASYNC_FLUSH_1(GND),
                        .ASYNC_FLUSH_S0(GND),
                        .ASYNC_FLUSH_S1(GND),
                        .CLK1_0(WClk), 
                        .CLK1_1(WClk),
                        .CLK1S_0(WClk0_Sel),
                        .CLK1S_1(WClk0_Sel), 
                        .CLK1EN_0(WClk_En), 
                        .CLK1EN_1(WClk_En), 
                        .CLK2_0(RClk),
                        .CLK2_1(RClk),
                        .CLK2S_0(RClk0_Sel),
                        .CLK2S_1(RClk0_Sel), 
                        .CLK2EN_0(RClk_En), 
                        .CLK2EN_1(RClk_En), 
                        .CONCAT_EN_0(VCC),
                        .CONCAT_EN_1(GND), 
                        .CS1_0(WD0_SEL), 
                        .CS1_1(GND), 
                        .CS2_0(RD0_SEL), 
                        .CS2_1(GND), 
                        .DIR_0(GND),
                        .DIR_1(GND), 
                        .FIFO_EN_0(GND), 
                        .FIFO_EN_1(GND), 
                        .P1_0(GND), 
                        .P1_1(GND), 
                        .P2_0(GND),
                        .P2_1(GND), 
                        .PIPELINE_RD_0(reg_rd0), 
                        .PIPELINE_RD_1(GND), 
                        .SYNC_FIFO_0(GND),
                        .SYNC_FIFO_1(GND), 
                        .WD_1({18{GND}}), 
                        .WD_0({1'b0,in_reg0[15:8],1'b0,in_reg0[7:0]}), 
			.WIDTH_SELECT1_0(WS1_0), 
			.WIDTH_SELECT1_1(WS_GND), 
			.WIDTH_SELECT2_0(WS2_0),
			.WIDTH_SELECT2_1(WS_GND), 
			.WEN1_0(wen_reg0[1:0]), 
			.WEN1_1(wen_reg0[3:2]), 
			.Almost_Empty_0(),
			.Almost_Empty_1(), 
			.Almost_Full_0(), 
			.Almost_Full_1(),
			.POP_FLAG_0(), 
			.POP_FLAG_1(), 
			.PUSH_FLAG_0(), 
			.PUSH_FLAG_1(),
			.RD_0({out_par0[1],out_reg0[15:8],out_par0[0],out_reg0[7:0]}), 
			.RD_1(),
			.SD(SD),
			.SD_RB1(SD_RB1),
			.LS(LS),
			.LS_RB1(LS_RB1),
			.DS(DS),
			.DS_RB1(DS_RB1),
			.TEST1A(GND),
			.TEST1B(GND),
			.RMA(4'd0),
			.RMB(4'd0),
			.RMEA(GND),
			.RMEB(GND)
			);	
  	end
	else if (data_width_int > 16)  begin

    	     ram8k_2x1_cell_macro # (
                        `include "bram_init_32.vh"
                           )
			_TECHMAP_REPLACE_ (
                        .A1_0(addr_wr0) , 
                        .A1_1(addr_wr1), 
                        .A2_0(addr_rd0), 
                        .A2_1(addr_rd1), 
                        .ASYNC_FLUSH_0(GND), 
                        .ASYNC_FLUSH_1(GND),
                        .ASYNC_FLUSH_S0(GND),
                        .ASYNC_FLUSH_S1(GND),
                        .CLK1_0(WClk), 
                        .CLK1_1(WClk),
                        .CLK1S_0(WClk0_Sel),
                        .CLK1S_1(WClk0_Sel), 
                        .CLK1EN_0(WClk_En), 
                        .CLK1EN_1(WClk_En), 
                        .CLK2_0(RClk),
                        .CLK2_1(RClk),
                        .CLK2S_0(RClk0_Sel),
                        .CLK2S_1(RClk0_Sel), 
                        .CLK2EN_0(RClk_En), 
                        .CLK2EN_1(RClk_En), 
                        .CONCAT_EN_0(VCC),
                        .CONCAT_EN_1(GND), 
                        .CS1_0(WD0_SEL), 
                        .CS1_1(GND), 
                        .CS2_0(RD0_SEL), 
                        .CS2_1(GND), 
                        .DIR_0(GND),
                        .DIR_1(GND), 
                        .FIFO_EN_0(GND), 
                        .FIFO_EN_1(GND), 
                        .P1_0(GND), 
                        .P1_1(GND), 
                        .P2_0(GND),
                        .P2_1(GND), 
                        .PIPELINE_RD_0(reg_rd0), 
                        .PIPELINE_RD_1(GND), 
                        .SYNC_FIFO_0(GND),
                        .SYNC_FIFO_1(GND), 
                        .WD_1({1'b0,in_reg0[31:24],1'b0,in_reg0[23:16]}), 
                        .WD_0({1'b0,in_reg0[15:8],1'b0,in_reg0[7:0]}), 
                        .WIDTH_SELECT1_0(WS1_0), 
                        .WIDTH_SELECT1_1(WS_GND), 
                        .WIDTH_SELECT2_0(WS2_0),
                        .WIDTH_SELECT2_1(WS_GND), 
                        .WEN1_0(wen_reg0[1:0]), 
                        .WEN1_1(wen_reg0[3:2]), 
                        .Almost_Empty_0(),
                        .Almost_Empty_1(), 
                        .Almost_Full_0(), 
                        .Almost_Full_1(),
                        .POP_FLAG_0(), 
                        .POP_FLAG_1(), 
                        .PUSH_FLAG_0(), 
                        .PUSH_FLAG_1(),
                        .RD_0({out_par0[1],out_reg0[15:8],out_par0[0],out_reg0[7:0]}), 
                        .RD_1({out_par0[3],out_reg0[31:24],out_par0[2],out_reg0[23:16]}),
                        .SD(SD),
                        .SD_RB1(SD_RB1),
                        .LS(LS),
                        .LS_RB1(LS_RB1),
                        .DS(DS),
                        .DS_RB1(DS_RB1),
                        .TEST1A(GND),
                        .TEST1B(GND),
                        .RMA(4'd0),
                        .RMB(4'd0),
                        .RMEA(GND),
                        .RMEB(GND)
                        );	
  	end
  	else 
  	begin
    	     wire TECHMAP_FAIL = 1'b1;
  	end
						
endgenerate	

	assign RD[data_width_int-1 :0]= out_reg0[data_width_int-1 :0];

endmodule


module FIFO_8K_BLK(DIN,Fifo_Push_Flush,Fifo_Pop_Flush,PUSH,POP,Push_Clk,Pop_Clk,Push_Clk_En,Pop_Clk_En,Fifo_Dir,Async_Flush,Almost_Full,Almost_Empty,PUSH_FLAG,POP_FLAG,DOUT);
					
parameter data_depth_int = 512,
          data_width_int = 36,
          reg_rd_int     = 0,
          sync_fifo_int  = 0;
			
input Fifo_Push_Flush,Fifo_Pop_Flush;
input Push_Clk,Pop_Clk;
input PUSH,POP;
input [data_width_int-1:0] DIN;
input Push_Clk_En,Pop_Clk_En,Fifo_Dir,Async_Flush;
output [data_width_int-1:0] DOUT;
output [3:0] PUSH_FLAG,POP_FLAG;
output Almost_Full,Almost_Empty;

wire LS,DS,SD,LS_RB1,DS_RB1,SD_RB1;
wire VCC,GND;

wire [10:0] addr_wr,addr_rd;
wire clk1_sig0, clk2_sig0, clk1_sig_en0, clk2_sig_en0, fifo_clk1_flush_sig0, fifo_clk2_flush_sig0, p1_sig0, p2_sig0,clk1_sig_sel0,clk2_sig_sel0;
wire reg_rd0,sync_fifo0; 
wire [15:0] in_reg0;
wire [15:0] out_reg0;
wire [1:0] WS1_0;
wire [1:0] WS2_0;
wire Push_Clk0_Sel,Pop_Clk0_Sel;
wire Async_Flush_Sel0;

wire [1:0] out_par0;

assign LS = 1'b0;
assign DS = 1'b0;
assign SD = 1'b0;
assign LS_RB1 = 1'b0;
assign DS_RB1 = 1'b0;
assign SD_RB1 = 1'b0;

assign VCC = 1'b1;
assign GND = 1'b0;

assign Push_Clk0_Sel  	= 1'b0;
assign Pop_Clk0_Sel   	= 1'b0;
assign Async_Flush_Sel0 = 1'b0;

assign reg_rd0 = reg_rd_int;
assign sync_fifo0 = sync_fifo_int;

assign addr_wr=11'b00000000000;
assign addr_rd=11'b00000000000;

assign clk1_sig0 = Fifo_Dir ? Pop_Clk : Push_Clk;
assign clk2_sig0 = Fifo_Dir ? Push_Clk : Pop_Clk ;
assign clk1_sig_en0 = Fifo_Dir ? Pop_Clk_En : Push_Clk_En;
assign clk2_sig_en0 = Fifo_Dir ? Push_Clk_En : Pop_Clk_En ;
assign clk1_sig_sel0 =  Push_Clk0_Sel;
assign clk2_sig_sel0 =  Pop_Clk0_Sel ;
assign fifo_clk1_flush_sig0 = Fifo_Dir ? Fifo_Pop_Flush : Fifo_Push_Flush;
assign fifo_clk2_flush_sig0 = Fifo_Dir ? Fifo_Push_Flush : Fifo_Pop_Flush ;
assign p1_sig0 = Fifo_Dir ? POP : PUSH;
assign p2_sig0 = Fifo_Dir ? PUSH : POP ;

generate 

	if (data_width_int == 16) 
	begin
    	     assign in_reg0[data_width_int-1:0] =DIN[data_width_int-1:0]; 
  	end  
  	else if (data_width_int > 8 && data_width_int < 16)
  	begin
	     assign in_reg0[15:data_width_int] =0;
    	     assign in_reg0[data_width_int-1:0] =DIN[data_width_int-1:0]; 
  	end
  	else if (data_width_int <= 8) 
	begin
	     assign in_reg0[15:data_width_int] =0;
    	     assign in_reg0[data_width_int-1:0] =DIN[data_width_int-1:0]; 
  	end

	if(data_width_int <=8)
  	begin
	     assign WS1_0 = 2'b00;
	     assign WS2_0 = 2'b00;
  	end
	else if(data_width_int >8 && data_width_int <=16)
  	begin
	     assign WS1_0 = 2'b01;
	     assign WS2_0 = 2'b01;
  	end
	else if(data_width_int > 16)
  	begin
	     assign WS1_0 = 2'b10;
	     assign WS2_0 = 2'b10;
  	end

endgenerate

	ram8k_2x1_cell_macro 
          _TECHMAP_REPLACE_(
		  	.A1_0(addr_wr) , 
			.A1_1(addr_wr), 
			.A2_0(addr_rd), 
			.A2_1(addr_rd), 
			.ASYNC_FLUSH_0(Async_Flush), 
			.ASYNC_FLUSH_1(GND),
			.ASYNC_FLUSH_S0(Async_Flush_Sel0), 
			.ASYNC_FLUSH_S1(GND),
			.CLK1_0(clk1_sig0), 
			.CLK1_1(GND), 
			.CLK1EN_0(clk1_sig_en0), 
			.CLK1EN_1(GND), 
			.CLK2_0(clk2_sig0),
			.CLK2_1(GND), 
			.CLK1S_0(clk1_sig_sel0), 
			.CLK1S_1(GND), 
			.CLK2S_0(clk2_sig_sel0),
			.CLK2S_1(GND),
			.CLK2EN_0(clk2_sig_en0), 
			.CLK2EN_1(GND), 
			.CONCAT_EN_0(GND),
			.CONCAT_EN_1(GND), 
			.CS1_0(fifo_clk1_flush_sig0), 
			.CS1_1(GND), 
			.CS2_0(fifo_clk2_flush_sig0), 
			.CS2_1(GND), 
			.DIR_0(Fifo_Dir),
			.DIR_1(GND), 
			.FIFO_EN_0(VCC), 
			.FIFO_EN_1(GND), 
			.P1_0(p1_sig0), 
			.P1_1(GND), 
			.P2_0(p2_sig0),
			.P2_1(GND), 
			.PIPELINE_RD_0(reg_rd0), 
			.PIPELINE_RD_1(GND), 
			.SYNC_FIFO_0(sync_fifo0),
			.SYNC_FIFO_1(GND), 
			.WD_1({18{GND}}), 
			.WD_0({1'b0,in_reg0[15:8],1'b0,in_reg0[7:0]}), 
			.WIDTH_SELECT1_0(WS1_0), 
			.WIDTH_SELECT1_1({GND,GND}), 
			.WIDTH_SELECT2_0(WS2_0),
			.WIDTH_SELECT2_1({GND,GND}), 
			.WEN1_0({GND,GND}), 
			.WEN1_1({GND,GND}), 
			.Almost_Empty_0(Almost_Empty),
			.Almost_Empty_1(), 
			.Almost_Full_0(Almost_Full), 
			.Almost_Full_1(),
			.POP_FLAG_0(POP_FLAG), 
			.POP_FLAG_1(), 
			.PUSH_FLAG_0(PUSH_FLAG), 
			.PUSH_FLAG_1(),
			.RD_0({out_par0[1],out_reg0[15:8],out_par0[0],out_reg0[7:0]}), 
			.RD_1(),
			.SD(SD),
			.SD_RB1(SD_RB1),
			.LS(LS),
			.LS_RB1(LS_RB1),
			.DS(DS),
			.DS_RB1(DS_RB1),
			.TEST1A(GND),
			.TEST1B(GND),
			.RMA(4'd0),
			.RMB(4'd0),
			.RMEA(GND),
			.RMEB(GND)
			);	
						
    	assign DOUT[data_width_int-1 :0]= out_reg0[data_width_int-1 :0];

endmodule


module FIFO_16K_BLK(DIN,Fifo_Push_Flush,Fifo_Pop_Flush,PUSH,POP,Push_Clk,Pop_Clk,Push_Clk_En,Pop_Clk_En,Fifo_Dir,Async_Flush,Almost_Full,Almost_Empty,PUSH_FLAG,POP_FLAG,DOUT);
					
parameter data_depth_int  = 512,
          data_width_int  = 36,
          reg_rd_int      = 0,
	  sync_fifo_int   = 0;
			
input Fifo_Push_Flush,Fifo_Pop_Flush;
input Push_Clk,Pop_Clk;
input PUSH,POP;
input [data_width_int-1:0] DIN;
input Push_Clk_En,Pop_Clk_En,Fifo_Dir,Async_Flush;
output [data_width_int-1:0] DOUT;
output [3:0] PUSH_FLAG,POP_FLAG;
output Almost_Full,Almost_Empty;

wire LS,DS,SD,LS_RB1,DS_RB1,SD_RB1;
wire VCC,GND;

wire [10:0] addr_wr,addr_rd;
wire clk1_sig0, clk2_sig0, clk1_sig_en0, clk2_sig_en0, fifo_clk1_flush_sig0, fifo_clk2_flush_sig0, p1_sig0, p2_sig0,clk1_sig_sel0,clk2_sig_sel0;
wire reg_rd0,sync_fifo0; 
wire [31:0] in_reg0;
wire [31:0] out_reg0;
wire [1:0] WS1_0;
wire [1:0] WS2_0;
wire Push_Clk0_Sel,Pop_Clk0_Sel;
wire Async_Flush_Sel0;

wire [3:0] out_par0;
wire [1:0] out_par1;

assign LS = 1'b0;
assign DS = 1'b0;
assign SD = 1'b0;
assign LS_RB1 = 1'b0;
assign DS_RB1 = 1'b0;
assign SD_RB1 = 1'b0;

assign VCC = 1'b1;
assign GND = 1'b0;

assign Push_Clk0_Sel  	= 1'b0;
assign Pop_Clk0_Sel   	= 1'b0;
assign Async_Flush_Sel0 = 1'b0;

assign reg_rd0 = reg_rd_int;
assign sync_fifo0 = sync_fifo_int;

assign addr_wr=11'b00000000000;
assign addr_rd=11'b00000000000;

assign clk1_sig0 = Fifo_Dir ? Pop_Clk : Push_Clk;
assign clk2_sig0 = Fifo_Dir ? Push_Clk : Pop_Clk ;
assign clk1_sig_en0 = Fifo_Dir ? Pop_Clk_En : Push_Clk_En;
assign clk2_sig_en0 = Fifo_Dir ? Push_Clk_En : Pop_Clk_En ;
assign clk1_sig_sel0 =  Push_Clk0_Sel;
assign clk2_sig_sel0 =  Pop_Clk0_Sel ;
assign fifo_clk1_flush_sig0 = Fifo_Dir ? Fifo_Pop_Flush : Fifo_Push_Flush;
assign fifo_clk2_flush_sig0 = Fifo_Dir ? Fifo_Push_Flush : Fifo_Pop_Flush ;
assign p1_sig0 = Fifo_Dir ? POP : PUSH;
assign p2_sig0 = Fifo_Dir ? PUSH : POP ;

generate 
	if (data_width_int == 32) 
	begin
    	     assign in_reg0[data_width_int-1:0] =DIN[data_width_int-1:0]; 
  	end  
  	else if (data_width_int > 8 && data_width_int < 32)
  	begin
    	     assign in_reg0[31:data_width_int] =0;
    	     assign in_reg0[data_width_int-1:0] =DIN[data_width_int-1:0]; 
  	end
  	else if (data_width_int <= 8) 
	begin
	     assign in_reg0[31:data_width_int] =0;
    	     assign in_reg0[data_width_int-1:0] =DIN[data_width_int-1:0]; 
  	end

	if(data_width_int <=8)
  	begin
	     assign WS1_0 = 2'b00;
	     assign WS2_0 = 2'b00;
  	end
	else if(data_width_int >8 && data_width_int <=16)
   	begin
	     assign WS1_0 = 2'b01;
	     assign WS2_0 = 2'b01;
  	end
	else if(data_width_int > 16)
  	begin
	     assign WS1_0 = 2'b10;
	     assign WS2_0 = 2'b10;
  	end

	if (data_width_int <=16)   begin

	   ram8k_2x1_cell_macro
             _TECHMAP_REPLACE_(
		     	.A1_0(addr_wr) , 
			.A1_1(addr_wr), 
			.A2_0(addr_rd), 
			.A2_1(addr_rd), 
			.ASYNC_FLUSH_0(Async_Flush), 
			.ASYNC_FLUSH_1(GND),
			.ASYNC_FLUSH_S0(Async_Flush_Sel0), 
			.ASYNC_FLUSH_S1(Async_Flush_Sel0),
			.CLK1_0(clk1_sig0), 
			.CLK1_1(clk1_sig0), 
			.CLK1EN_0(clk1_sig_en0), 
			.CLK1EN_1(clk1_sig_en0), 
			.CLK2_0(clk2_sig0),
			.CLK2_1(clk2_sig0), 
			.CLK1S_0(clk1_sig_sel0), 
			.CLK1S_1(clk1_sig_sel0), 
			.CLK2S_0(clk2_sig_sel0),
			.CLK2S_1(clk2_sig_sel0),
			.CLK2EN_0(clk2_sig_en0), 
			.CLK2EN_1(clk2_sig_en0), 
			.CONCAT_EN_0(VCC),
			.CONCAT_EN_1(GND), 
			.CS1_0(fifo_clk1_flush_sig0), 
			.CS1_1(GND), 
			.CS2_0(fifo_clk2_flush_sig0), 
			.CS2_1(GND), 
			.DIR_0(Fifo_Dir),
			.DIR_1(GND), 
			.FIFO_EN_0(VCC), 
			.FIFO_EN_1(GND), 
			.P1_0(p1_sig0), 
			.P1_1(GND), 
			.P2_0(p2_sig0),
			.P2_1(GND), 
			.PIPELINE_RD_0(reg_rd0), 
			.PIPELINE_RD_1(GND), 
			.SYNC_FIFO_0(sync_fifo0),
			.SYNC_FIFO_1(GND), 
			.WD_1({18{GND}}), 
			.WD_0({1'b0,in_reg0[15:8],1'b0,in_reg0[7:0]}), 
			.WIDTH_SELECT1_0(WS1_0), 
			.WIDTH_SELECT1_1({GND,GND}), 
			.WIDTH_SELECT2_0(WS2_0),
			.WIDTH_SELECT2_1({GND,GND}), 
			.WEN1_0({GND,GND}), 
			.WEN1_1({GND,GND}), 
			.Almost_Empty_0(Almost_Empty),
			.Almost_Empty_1(), 
			.Almost_Full_0(Almost_Full), 
			.Almost_Full_1(),
			.POP_FLAG_0(POP_FLAG), 
			.POP_FLAG_1(), 
			.PUSH_FLAG_0(PUSH_FLAG), 
			.PUSH_FLAG_1(),
			.RD_0({out_par0[1],out_reg0[15:8],out_par0[0],out_reg0[7:0]}), 
			.RD_1(),
			.SD(SD),
			.SD_RB1(SD_RB1),
			.LS(LS),
			.LS_RB1(LS_RB1),
			.DS(DS),
			.DS_RB1(DS_RB1),
			.TEST1A(GND),
			.TEST1B(GND),
			.RMA(4'd0),
			.RMB(4'd0),
			.RMEA(GND),
			.RMEB(GND)
			);	

  	end
  	else if (data_width_int > 16)	begin
	
    	    ram8k_2x1_cell_macro 
               _TECHMAP_REPLACE_(
              		.A1_0(addr_wr) , 
			.A1_1(addr_wr), 
			.A2_0(addr_rd), 
			.A2_1(addr_rd), 
			.ASYNC_FLUSH_0(Async_Flush), 
			.ASYNC_FLUSH_1(GND),
			.ASYNC_FLUSH_S0(Async_Flush_Sel0), 
			.ASYNC_FLUSH_S1(Async_Flush_Sel0),
			.CLK1_0(clk1_sig0), 
			.CLK1_1(clk1_sig0), 
			.CLK1EN_0(clk1_sig_en0), 
			.CLK1EN_1(clk1_sig_en0), 
			.CLK2_0(clk2_sig0),
			.CLK2_1(clk2_sig0), 
			.CLK1S_0(clk1_sig_sel0), 
			.CLK1S_1(clk1_sig_sel0), 
			.CLK2S_0(clk2_sig_sel0),
			.CLK2S_1(clk2_sig_sel0),
			.CLK2EN_0(clk2_sig_en0), 
			.CLK2EN_1(clk2_sig_en0), 
			.CONCAT_EN_0(VCC),
			.CONCAT_EN_1(GND), 
			.CS1_0(fifo_clk1_flush_sig0), 
			.CS1_1(GND), 
			.CS2_0(fifo_clk2_flush_sig0), 
			.CS2_1(GND), 
			.DIR_0(Fifo_Dir),
			.DIR_1(GND), 
			.FIFO_EN_0(VCC), 
			.FIFO_EN_1(GND), 
			.P1_0(p1_sig0), 
			.P1_1(GND), 
			.P2_0(p2_sig0),
			.P2_1(GND), 
			.PIPELINE_RD_0(reg_rd0), 
			.PIPELINE_RD_1(GND), 
			.SYNC_FIFO_0(sync_fifo0),
			.SYNC_FIFO_1(GND), 
			.WD_1({1'b0,in_reg0[31:24],1'b0,in_reg0[23:16]}), 
			.WD_0({1'b0,in_reg0[15:8],1'b0,in_reg0[7:0]}), 
			.WIDTH_SELECT1_0(WS1_0), 
			.WIDTH_SELECT1_1({GND,GND}), 
			.WIDTH_SELECT2_0(WS2_0),
			.WIDTH_SELECT2_1({GND,GND}), 
			.WEN1_0({GND,GND}), 
			.WEN1_1({GND,GND}), 
			.Almost_Empty_0(Almost_Empty),
			.Almost_Empty_1(), 
			.Almost_Full_0(Almost_Full), 
			.Almost_Full_1(),
			.POP_FLAG_0(POP_FLAG), 
			.POP_FLAG_1(), 
			.PUSH_FLAG_0(PUSH_FLAG), 
			.PUSH_FLAG_1(),
			.RD_0({out_par0[1],out_reg0[15:8],out_par0[0],out_reg0[7:0]}), 
			.RD_1({out_par0[3],out_reg0[31:24],out_par0[2],out_reg0[23:16]}),
			.SD(SD),
			.SD_RB1(SD_RB1),
			.LS(LS),
			.LS_RB1(LS_RB1),
			.DS(DS),
			.DS_RB1(DS_RB1),
			.TEST1A(GND),
			.TEST1B(GND),
			.RMA(4'd0),
			.RMB(4'd0),
			.RMEA(GND),
			.RMEB(GND)
			);
  	end              

endgenerate

  	assign DOUT[data_width_int-1 :0]= out_reg0[data_width_int-1 :0];

endmodule
