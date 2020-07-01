module FIFO_16K_BLK(DIN0,Fifo_Push_Flush0,Fifo_Pop_Flush0,PUSH0,POP0,Push_Clk0,Pop_Clk0,Push_Clk0_En,Pop_Clk0_En,Fifo0_Dir,Async_Flush0,Almost_Full0,Almost_Empty0,PUSH_FLAG0,POP_FLAG0,DOUT0,
					DIN1,Fifo_Push_Flush1,Fifo_Pop_Flush1,PUSH1,POP1,Push_Clk1,Pop_Clk1,Push_Clk1_En,Pop_Clk1_En,Fifo1_Dir,Async_Flush1,Almost_Full1,Almost_Empty1,PUSH_FLAG1,POP_FLAG1,DOUT1,
					LS,DS,SD,LS_RB1,DS_RB1,SD_RB1 );
					
parameter 	Concatenation_En = 0,

			wr_depth_int0  	= 512,
			rd_depth_int0  	= 512,
			wr_width_int0  	= 36,
			rd_width_int0  	= 36,
			reg_rd_int0    	= 0,
			sync_fifo_int0 	= 0,
			
			wr_depth_int1  = 512,
			rd_depth_int1  = 512,
			wr_width_int1  = 18,
			rd_width_int1  = 18,
			reg_rd_int1    = 0,
			sync_fifo_int1 = 0;

input Fifo_Push_Flush0,Fifo_Pop_Flush0;
input Push_Clk0,Pop_Clk0;
input PUSH0,POP0;
input [wr_width_int0-1:0] DIN0;
input Push_Clk0_En,Pop_Clk0_En,Fifo0_Dir,Async_Flush0;
output [rd_width_int0-1:0] DOUT0;
output [3:0] PUSH_FLAG0,POP_FLAG0;
output Almost_Full0,Almost_Empty0;

input Fifo_Push_Flush1,Fifo_Pop_Flush1;
input Push_Clk1,Pop_Clk1;
input PUSH1,POP1;
input [wr_width_int1-1:0] DIN1;
input Push_Clk1_En,Pop_Clk1_En,Fifo1_Dir,Async_Flush1;
output [rd_width_int1-1:0] DOUT1;
output [3:0] PUSH_FLAG1,POP_FLAG1;
output Almost_Full1,Almost_Empty1;

input LS,DS,SD,LS_RB1,DS_RB1,SD_RB1;

wire [10:0] addr_wr,addr_rd;
wire clk1_sig0, clk2_sig0, clk1_sig_en0, clk2_sig_en0, fifo_clk1_flush_sig0, fifo_clk2_flush_sig0, p1_sig0, p2_sig0,clk1_sig_sel0,clk2_sig_sel0;
wire reg_rd0,sync_fifo0; 
wire [35:0] in_reg0;
wire [35:0] out_reg0;
wire [1:0] WS1_0;
wire [1:0] WS2_0;
wire Push_Clk0_Sel,Pop_Clk0_Sel;
wire Async_Flush_Sel0;


wire clk1_sig1, clk2_sig1, clk1_sig_en1, clk2_sig_en1, fifo_clk1_flush_sig1, fifo_clk2_flush_sig1, p1_sig1, p2_sig1,clk1_sig_sel1,clk2_sig_sel1;
wire reg_rd1,sync_fifo1;
wire [35:0] in_reg1;
wire [35:0] out_reg1;
wire [1:0] WS1_1;
wire [1:0] WS2_1;
wire Push_Clk1_Sel,Pop_Clk1_Sel;
wire Async_Flush_Sel1;


parameter depth_level1 = 512;
parameter depth_level2 = 1024;
parameter depth_level3 = 2048;

parameter mod2_0 =(wr_width_int0)%2;
parameter mod4_0 =(wr_width_int0)%4;

parameter mod2_1 =(wr_width_int1)%2;
parameter mod4_1 =(wr_width_int1)%4;

parameter zero0_36_2= (36-wr_width_int0) / 2;
parameter zero0_36_2_odd=(36-wr_width_int0+1)/2;
parameter zero0_18_2_odd= (18-wr_width_int0+1)/2;
parameter zero0_36_4_1=(36-wr_width_int0+1)/4;
parameter zero0_36_4_2=(36-wr_width_int0+2)/4;
parameter zero0_36_4_3=(36-wr_width_int0+3)/4;
parameter zero0_36_4 = (36- wr_width_int0) /4 ;
parameter zero0_18_2=(18-wr_width_int0)/2;
parameter by0_2 = (wr_width_int0)/2;
parameter by0_4 = (wr_width_int0)/4;
parameter by0_4_2= (wr_width_int0/4)*2;
parameter by0_4_3=(wr_width_int0/4)*3;
parameter zero0_18_2_rg = 18-wr_width_int0;
parameter zero0_9_2_rg = 9-wr_width_int0;
parameter by0_2_read= (rd_width_int0)/2;
parameter by0_4_read = (rd_width_int0)/4;
parameter by0_4_readx2=(rd_width_int0/4)*2;
parameter by0_4_readx3=(rd_width_int0/4)*3;

parameter zero1_36_2= (36-wr_width_int1) / 2;
parameter zero1_36_2_odd=(36-wr_width_int1+1)/2;
parameter zero1_18_2_odd= (18-wr_width_int1+1)/2;
parameter zero1_36_4_1=(36-wr_width_int1+1)/4;
parameter zero1_36_4_2=(36-wr_width_int1+2)/4;
parameter zero1_36_4_3=(36-wr_width_int1+3)/4;
parameter zero1_36_4 = (36- wr_width_int1) /4 ;
parameter zero1_18_2=(18-wr_width_int1)/2;
parameter by1_2 = (wr_width_int1)/2;
parameter by1_4 = (wr_width_int1)/4;
parameter by1_4_2= (wr_width_int1/4)*2;
parameter by1_4_3=(wr_width_int1/4)*3;
parameter zero1_9_2_rg = 9-wr_width_int1;
parameter by1_2_read= (rd_width_int1)/2;

assign VCC = 1'b1;
assign GND = 1'b0;

assign Push_Clk0_Sel  	= 1'b0;
assign Pop_Clk0_Sel   	= 1'b0;
assign Async_Flush_Sel0 = 1'b0;

assign reg_rd0 = reg_rd_int0;
assign sync_fifo0 = sync_fifo_int0;

generate
begin
	assign addr_wr=11'b00000000000;
	assign addr_rd=11'b00000000000;
end
endgenerate

assign clk1_sig0 = Fifo0_Dir ? Pop_Clk0 : Push_Clk0;
assign clk2_sig0 = Fifo0_Dir ? Push_Clk0 : Pop_Clk0 ;
assign clk1_sig_en0 = Fifo0_Dir ? Pop_Clk0_En : Push_Clk0_En;
assign clk2_sig_en0 = Fifo0_Dir ? Push_Clk0_En : Pop_Clk0_En ;
assign clk1_sig_sel0 =  Push_Clk0_Sel;
assign clk2_sig_sel0 =  Pop_Clk0_Sel ;
assign fifo_clk1_flush_sig0 = Fifo0_Dir ? Fifo_Pop_Flush0 : Fifo_Push_Flush0;
assign fifo_clk2_flush_sig0 = Fifo0_Dir ? Fifo_Push_Flush0 : Fifo_Pop_Flush0 ;
assign p1_sig0 = Fifo0_Dir ? POP0 : PUSH0;
assign p2_sig0 = Fifo0_Dir ? PUSH0 : POP0 ;

generate 
//Generating data
if (Concatenation_En == 1'b0) begin
	assign clk1_sig1 = Fifo1_Dir ? Pop_Clk1 : Push_Clk1;
	assign clk2_sig1 = Fifo1_Dir ? Push_Clk1 : Pop_Clk1 ;
	assign clk1_sig_en1 = Fifo1_Dir ? Pop_Clk1_En : Push_Clk1_En;
	assign clk2_sig_en1 = Fifo1_Dir ? Push_Clk1_En : Pop_Clk1_En ;
	assign clk1_sig_sel1 =  Push_Clk1_Sel;
	assign clk2_sig_sel1 =  Pop_Clk1_Sel ;
	assign fifo_clk1_flush_sig1 = Fifo1_Dir ? Fifo_Pop_Flush1 : Fifo_Push_Flush1;
	assign fifo_clk2_flush_sig1 = Fifo1_Dir ? Fifo_Push_Flush1 : Fifo_Pop_Flush1 ;
	assign p1_sig1 = Fifo1_Dir ? POP1 : PUSH1;
	assign p2_sig1 = Fifo1_Dir ? PUSH1 : POP1 ;
	assign reg_rd1 = reg_rd_int1;
	assign sync_fifo1 = sync_fifo_int1;
	assign Push_Clk1_Sel  	= 1'b0;
	assign Pop_Clk1_Sel   	= 1'b0;
	assign Async_Flush_Sel1 = 1'b0;
end

if(wr_width_int0 == 1)
begin
	assign in_reg0[35:wr_width_int0]=0;
	assign in_reg0[0]= DIN0[0]; 
end 
else if (wr_width_int0 ==36 || wr_width_int0 == 18 || wr_width_int0 ==9)
begin
	assign in_reg0[35:wr_width_int0]=0;
	assign in_reg0[wr_width_int0-1:0]=DIN0;
end
else if(wr_width_int0 ==35 || (wr_width_int0 ==17 && wr_depth_int0 ==depth_level2) ||(wr_width_int0==17 && wr_depth_int0 ==depth_level1 && rd_depth_int0 != depth_level3) || (wr_width_int0==8&&wr_depth_int0==depth_level3) || (wr_width_int0 ==8 && wr_depth_int0 ==depth_level2 && rd_depth_int0 != depth_level3))
begin
	assign in_reg0[wr_width_int0:wr_width_int0]=0;				 
	assign in_reg0[wr_width_int0-1 :0]=DIN0;
end
else if(wr_width_int0 == rd_width_int0)
begin
	assign in_reg0[35:wr_width_int0]=0;
	assign in_reg0[wr_width_int0 -1 :0]=DIN0;
end
else if(wr_width_int0 ==34 && rd_depth_int0 ==depth_level3 ) 
begin
	assign in_reg0[35]=0;
	assign in_reg0[26]=0;
	assign in_reg0[34:27]=DIN0[33:26];
	assign in_reg0[25:18]=DIN0[25:18];
	assign in_reg0[17:0]=DIN0[17:0];
end
else if(wr_width_int0 ==33 && rd_depth_int0 ==depth_level3 )
begin
	assign in_reg0[35]=0;
	assign in_reg0[26]=0;
	assign in_reg0[17]=0;
	assign in_reg0[34:27]=DIN0[33:26];
	assign in_reg0[25:18]=DIN0[25:18];
	assign in_reg0[16:0]=DIN0[17:0];
end
else if(wr_depth_int0 == depth_level1)
begin
	if(rd_depth_int0 == depth_level2)
	begin
		if(wr_width_int0 > 18)
		begin
			if(mod2_0 ==0)
        	begin
				assign in_reg0[17 : 18-zero0_36_2]=0;
				assign in_reg0[35 :  36-zero0_36_2]=0  ;            
                assign in_reg0[18-zero0_36_2-1:0]=DIN0[by0_2-1:0] ;
                assign in_reg0[36-zero0_36_2-1:18]= DIN0[wr_width_int0-1:by0_2];
            end
			else
			begin
				assign in_reg0[35:36-zero0_36_2_odd]=0;
				assign in_reg0[17:18-zero0_36_2_odd+1]=0;
				assign in_reg0[36-zero0_36_2_odd-1:18]=DIN0[wr_width_int0-1:by0_2+1];
				assign in_reg0[18-zero0_36_2_odd:0]=DIN0[by0_2:0];
			end
		end
		else
		begin
			if(mod2_0==0)
			begin
				assign in_reg0[8:9-zero0_18_2]=0;
				assign in_reg0[17: 18-zero0_18_2]=0;
				assign in_reg0[9-zero0_18_2-1:0]=DIN0[ by0_2-1:0];
				assign in_reg0[18-zero0_18_2:9]=DIN0[wr_width_int0-1:by0_2];
			end
			else
			begin
				assign in_reg0[17:18-zero0_18_2_odd]=0;
				assign in_reg0[8:9-zero0_18_2_odd+1]=0;
				assign in_reg0[18-zero0_18_2_odd-1:9]=DIN0[wr_width_int0-1:by0_2+1];
				assign in_reg0[9-zero0_18_2_odd:0]=DIN0[by0_2:0];
			end
		end
	end
	else if(rd_depth_int0 == depth_level3 )
	begin
		if(mod4_0 == 0)
		begin
			assign in_reg0[35:36-zero0_36_4] = 0;
			assign in_reg0[26:27- zero0_36_4]=0;
			assign in_reg0[17:18-zero0_36_4]=0;
			assign in_reg0[8:9-zero0_36_4]=0;
			assign in_reg0[36-zero0_36_4-1:27]=DIN0[wr_width_int0-1:by0_4_3];
			assign in_reg0[27-zero0_36_4-1:18]= DIN0[by0_4_3-1:by0_4_2];
			assign in_reg0[18-zero0_36_4-1:9]=DIN0[by0_4_2-1:by0_4];
			assign in_reg0[9-zero0_36_4-1:0]=DIN0[by0_4-1:0];
		end
		else if (mod4_0==1)
		begin
			assign in_reg0[35:36-zero0_36_4_3]=0;
			assign in_reg0[26:27-zero0_36_4_3]=0;
			assign in_reg0[17:18-zero0_36_4_3]=0;
			assign in_reg0[8:9-zero0_36_4_3+1]=0;
			assign in_reg0[36-zero0_36_4_3-1:27]=DIN0[wr_width_int0-1:by0_4_3+1];
			assign in_reg0[27-zero0_36_4_3-1:18]=DIN0[by0_4_3:by0_4_2+1];
			assign in_reg0[18-zero0_36_4_3-1:9]=DIN0[by0_4_2:by0_4+1];
			assign in_reg0[9-zero0_36_4_3:0]=DIN0[by0_4:0];
		end
		else if (mod4_0==2)
		begin
			assign in_reg0[35:36-zero0_36_4_2]=0;
			assign in_reg0[26:27-zero0_36_4_2]=0;
			assign in_reg0[17:18-zero0_36_4_2+1]=0;
			assign in_reg0[8:9-zero0_36_4_2+1]=0;
			assign in_reg0[36-zero0_36_4_2-1:27]=DIN0[wr_width_int0-1:by0_4_3+2];
			assign in_reg0[27-zero0_36_4_2-1:18]=DIN0[by0_4_3+1:by0_4_2+2];
			assign in_reg0[18-zero0_36_4_2:9]=DIN0[by0_4_2+1:by0_4+1];
			assign in_reg0[9-zero0_36_4_2:0]=DIN0[by0_4:0];
		end
		else if (mod4_0==3)
		begin
			assign in_reg0[35:36-zero0_36_4_1-1]=0;
			assign in_reg0[26:27-zero0_36_4_1]=0;
			assign in_reg0[17:18-zero0_36_4_1]=0;
			assign in_reg0[8:9-zero0_36_4_1]=0;
			assign in_reg0[36-zero0_36_4_1-2:27]=DIN0[wr_width_int0-1:by0_4_3+3];
			assign in_reg0[27-zero0_36_4_1-1:18]=DIN0[by0_4_3+2:by0_4_2+2];
			assign in_reg0[18-zero0_36_4_1-1:9]=DIN0[by0_4_2+1:by0_4+1];
			assign in_reg0[9-zero0_36_4_1-1:0]=DIN0[by0_4:0];
		end
	end
end
else if(wr_depth_int0 == depth_level2)
begin
	if(rd_depth_int0 == depth_level3)
	begin
		if(mod2_0==0)
		begin
			assign in_reg0[8:9-zero0_18_2]=0;
			assign in_reg0[17: 18-zero0_18_2]=0;
			assign in_reg0[9-zero0_18_2-1:0]=DIN0[ by0_2-1:0];
			assign in_reg0[18-zero0_18_2:9]=DIN0[wr_width_int0-1:by0_2];
		end
		else
		begin
			assign in_reg0[17:18-zero0_18_2_odd]=0;
			assign in_reg0[8:9-zero0_18_2_odd+1]=0;
			assign in_reg0[18-zero0_18_2_odd-1:9]=DIN0[wr_width_int0-1:by0_2+1];
			assign in_reg0[9-zero0_18_2_odd:0]=DIN0[by0_2:0];
		end
	end
	else
	begin
		assign in_reg0[35:wr_width_int0]=0;
		assign in_reg0[wr_width_int0-1:0]=DIN0;
	end
end
else
begin 
	assign in_reg0[35:wr_width_int0]=0;
	assign in_reg0[wr_width_int0-1:0]=DIN0;	
end	

if (Concatenation_En == 1'b0) begin
	if(wr_width_int1 == 1)
	begin
		assign in_reg1[35:wr_width_int1]=0;
		assign in_reg1[0]= DIN1[0]; 
	end 
	else if (wr_width_int1 ==36 || wr_width_int1 == 18 || wr_width_int1 ==9)
	begin
		assign in_reg1[35:wr_width_int1]=0;
		assign in_reg1[wr_width_int1-1:0]=DIN1;
	end
	else if(wr_width_int1 ==35 || (wr_width_int1 ==17 && wr_depth_int1 ==depth_level2) ||(wr_width_int1==17 && wr_depth_int1 ==depth_level1 && rd_depth_int1 != depth_level3) || (wr_width_int1==8&&wr_depth_int1==depth_level3) || (wr_width_int1 ==8 && wr_depth_int1 ==depth_level2 && rd_depth_int1 != depth_level3))
	begin
		assign in_reg1[wr_width_int1:wr_width_int1]=0;				 
		assign in_reg1[wr_width_int1-1 :0]=DIN1;
	end
	else if(wr_width_int1 == rd_width_int1)
	begin
		assign in_reg1[35:wr_width_int1]=0;
		assign in_reg1[wr_width_int1 -1 :0]=DIN1;
	end
	else if(wr_width_int1 ==34 && rd_depth_int1 ==depth_level3 ) 
	begin
		assign in_reg1[35]=0;
		assign in_reg1[26]=0;
		assign in_reg1[34:27]=DIN1[33:26];
		assign in_reg1[25:18]=DIN1[25:18];
		assign in_reg1[17:0]=DIN1[17:0];
	end
	else if(wr_width_int1 ==33 && rd_depth_int1 ==depth_level3 )
	begin
		assign in_reg1[35]=0;
		assign in_reg1[26]=0;
		assign in_reg1[17]=0;
		assign in_reg1[34:27]=DIN1[33:26];
		assign in_reg1[25:18]=DIN1[25:18];
		assign in_reg1[16:0]=DIN1[17:0];
	end
	else if(wr_depth_int1 == depth_level1)
	begin
		if(rd_depth_int1 == depth_level2)
		begin
			if(wr_width_int1 > 18)
			begin
				if(mod2_1 ==0)
				begin
					assign in_reg1[17 : 18-zero1_36_2]=0;
					assign in_reg1[35 :  36-zero1_36_2]=0  ;            
					assign in_reg1[18-zero1_36_2-1:0]=DIN1[by1_2-1:0] ;
					assign in_reg1[36-zero1_36_2-1:18]= DIN1[wr_width_int1-1:by1_2];
				end
				else
				begin
					assign in_reg1[35:36-zero1_36_2_odd]=0;
					assign in_reg1[17:18-zero1_36_2_odd+1]=0;
					assign in_reg1[36-zero1_36_2_odd-1:18]=DIN1[wr_width_int1-1:by1_2+1];
					assign in_reg1[18-zero1_36_2_odd:0]=DIN1[by1_2:0];
				end
			end
			else
			begin
				if(mod2_1==0)
				begin
					assign in_reg1[8:9-zero1_18_2]=0;
					assign in_reg1[17: 18-zero1_18_2]=0;
					assign in_reg1[9-zero1_18_2-1:0]=DIN1[ by1_2-1:0];
					assign in_reg1[18-zero1_18_2:9]=DIN1[wr_width_int1-1:by1_2];
				end
				else
				begin
					assign in_reg1[17:18-zero1_18_2_odd]=0;
					assign in_reg1[8:9-zero1_18_2_odd+1]=0;
					assign in_reg1[18-zero1_18_2_odd-1:9]=DIN1[wr_width_int1-1:by1_2+1];
					assign in_reg1[9-zero1_18_2_odd:0]=DIN1[by1_2:0];
				end
			end
		end
		else if(rd_depth_int1 == depth_level3 )
		begin
			if(mod4_1 == 0)
			begin
				assign in_reg1[35:36-zero1_36_4] = 0;
				assign in_reg1[26:27- zero1_36_4]=0;
				assign in_reg1[17:18-zero1_36_4]=0;
				assign in_reg1[8:9-zero1_36_4]=0;
				assign in_reg1[36-zero1_36_4-1:27]=DIN1[wr_width_int1-1:by1_4_3];
				assign in_reg1[27-zero1_36_4-1:18]= DIN1[by1_4_3-1:by1_4_2];
				assign in_reg1[18-zero1_36_4-1:9]=DIN1[by1_4_2-1:by1_4];
				assign in_reg1[9-zero1_36_4-1:0]=DIN1[by1_4-1:0];
			end
			else if (mod4_1==1)
			begin
				assign in_reg1[35:36-zero1_36_4_3]=0;
				assign in_reg1[26:27-zero1_36_4_3]=0;
				assign in_reg1[17:18-zero1_36_4_3]=0;
				assign in_reg1[8:9-zero1_36_4_3+1]=0;
				assign in_reg1[36-zero1_36_4_3-1:27]=DIN1[wr_width_int1-1:by1_4_3+1];
				assign in_reg1[27-zero1_36_4_3-1:18]=DIN1[by1_4_3:by1_4_2+1];
				assign in_reg1[18-zero1_36_4_3-1:9]=DIN1[by1_4_2:by1_4+1];
				assign in_reg1[9-zero1_36_4_3:0]=DIN1[by1_4:0];
			end
			else if (mod4_1==2)
			begin
				assign in_reg1[35:36-zero1_36_4_2]=0;
				assign in_reg1[26:27-zero1_36_4_2]=0;
				assign in_reg1[17:18-zero1_36_4_2+1]=0;
				assign in_reg1[8:9-zero1_36_4_2+1]=0;
				assign in_reg1[36-zero1_36_4_2-1:27]=DIN1[wr_width_int1-1:by1_4_3+2];
				assign in_reg1[27-zero1_36_4_2-1:18]=DIN1[by1_4_3+1:by1_4_2+2];
				assign in_reg1[18-zero1_36_4_2:9]=DIN1[by1_4_2+1:by1_4+1];
				assign in_reg1[9-zero1_36_4_2:0]=DIN1[by1_4:0];
			end
			else if (mod4_1==3)
			begin
				assign in_reg1[35:36-zero1_36_4_1-1]=0;
				assign in_reg1[26:27-zero1_36_4_1]=0;
				assign in_reg1[17:18-zero1_36_4_1]=0;
				assign in_reg1[8:9-zero1_36_4_1]=0;
				assign in_reg1[36-zero1_36_4_1-2:27]=DIN1[wr_width_int1-1:by1_4_3+3];
				assign in_reg1[27-zero1_36_4_1-1:18]=DIN1[by1_4_3+2:by1_4_2+2];
				assign in_reg1[18-zero1_36_4_1-1:9]=DIN1[by1_4_2+1:by1_4+1];
				assign in_reg1[9-zero1_36_4_1-1:0]=DIN1[by1_4:0];
			end
		end
	end
	else if(wr_depth_int1 == depth_level2)
	begin
		if(rd_depth_int1 == depth_level3)
		begin
			if(mod2_1==0)
			begin
				assign in_reg1[8:9-zero1_18_2]=0;
				assign in_reg1[17: 18-zero1_18_2]=0;
				assign in_reg1[9-zero1_18_2-1:0]=DIN1[ by1_2-1:0];
				assign in_reg1[18-zero1_18_2:9]=DIN1[wr_width_int1-1:by1_2];
			end
			else
			begin
				assign in_reg1[17:18-zero1_18_2_odd]=0;
				assign in_reg1[8:9-zero1_18_2_odd+1]=0;
				assign in_reg1[18-zero1_18_2_odd-1:9]=DIN1[wr_width_int1-1:by1_2+1];
				assign in_reg1[9-zero1_18_2_odd:0]=DIN1[by1_2:0];
			end
		end
		else
		begin
			assign in_reg1[35:wr_width_int1]=0;
			assign in_reg1[wr_width_int1-1:0]=DIN1;
		end
	end
	else
	begin 
		assign in_reg1[35:wr_width_int1]=0;
		assign in_reg1[wr_width_int1-1:0]=DIN1;	
	end	
end


if(rd_depth_int0 == depth_level3 && wr_depth_int0 == depth_level1)
	assign WS1_0 =2'b10;
else if(rd_depth_int0 == depth_level3 && wr_depth_int0 == depth_level2)
	assign WS1_0=2'b01;
else if(wr_depth_int0 == depth_level1 && wr_width_int0 <=9)
	assign WS1_0=2'b01;
else if(wr_width_int0 <=9)
	assign WS1_0 = 2'b00;
else if(wr_width_int0 >9 && wr_width_int0 <=18)
	assign WS1_0 = 2'b01;
else if(wr_width_int0 > 18)
	assign WS1_0 = 2'b10;

if(wr_depth_int0 == depth_level3 && rd_depth_int0 == depth_level1)
	assign WS2_0 = 2'b10;
else if(wr_depth_int0 == depth_level3  && rd_depth_int0 == depth_level2)
	assign WS2_0 = 2'b01;
else if(rd_depth_int0 == depth_level1 && rd_width_int0 <=9)
	assign WS2_0 = 2'b01;
else if(rd_width_int0 <= 9)
	assign WS2_0 = 2'b00;
else if((rd_width_int0 >9) && (rd_width_int0 <= 18))
	assign WS2_0 = 2'b01;
else if(rd_width_int0 >18)
	assign WS2_0 = 2'b10;

if (Concatenation_En == 1'b0) begin	
	if(wr_width_int1 <=9)
		assign WS1_1 = 2'b00;
	else if(wr_width_int1 >9 && wr_width_int1 <=18)
		assign WS1_1 = 2'b01;
	else if(wr_width_int1 > 18)
		assign WS1_1 = 2'b10;

	if(rd_width_int1 <= 9)
		assign WS2_1 = 2'b00;
	else if((rd_width_int1 >9) && (rd_width_int1 <= 18))
		assign WS2_1 = 2'b01;
	else if(rd_width_int1 >18)
		assign WS2_1 = 2'b10;
end


if (Concatenation_En == 1'b0)	

	ram8k_2x1_cell_macro U1 (.A1_0(addr_wr) , 
							.A1_1(addr_wr), 
							.A2_0(addr_rd), 
							.A2_1(addr_rd), 
							.ASYNC_FLUSH_0(Async_Flush0), 
							.ASYNC_FLUSH_1(Async_Flush1),
							.ASYNC_FLUSH_S0(Async_Flush_Sel0), 
							.ASYNC_FLUSH_S1(Async_Flush_Sel1), 
							.CLK1_0(clk1_sig0), 
							.CLK1_1(clk1_sig1), 
							.CLK1EN_0(clk1_sig_en0), 
							.CLK1EN_1(clk1_sig_en1), 
							.CLK2_0(clk2_sig0),
							.CLK2_1(clk2_sig1), 
							.CLK1S_0(clk1_sig_sel0), 
							.CLK1S_1(clk1_sig_sel1), 
							.CLK2S_0(clk2_sig_sel0),
							.CLK2S_1(clk2_sig_sel1),
							.CLK2EN_0(clk2_sig_en0), 
							.CLK2EN_1(clk2_sig_en1), 
							.CONCAT_EN_0(GND),
							.CONCAT_EN_1(GND), 
							.CS1_0(fifo_clk1_flush_sig0), 
							.CS1_1(fifo_clk1_flush_sig1), 
							.CS2_0(fifo_clk2_flush_sig0), 
							.CS2_1(fifo_clk2_flush_sig1), 
							.DIR_0(Fifo0_Dir),
							.DIR_1(Fifo1_Dir), 
							.FIFO_EN_0(VCC), 
							.FIFO_EN_1(VCC), 
							.P1_0(p1_sig0), 
							.P1_1(p1_sig1), 
							.P2_0(p2_sig0),
							.P2_1(p2_sig1), 
							.PIPELINE_RD_0(reg_rd0), 
							.PIPELINE_RD_1(reg_rd1), 
							.SYNC_FIFO_0(sync_fifo0),
							.SYNC_FIFO_1(sync_fifo1), 
							.WD_1(in_reg1[17:0]), 
							.WD_0(in_reg0[17:0]), 
							.WIDTH_SELECT1_0(WS1_0), 
							.WIDTH_SELECT1_1(WS1_1), 
							.WIDTH_SELECT2_0(WS2_0),
							.WIDTH_SELECT2_1(WS2_1), 
							// PP-II doesn't use this signal
							.WEN1_0({GND,GND}), 
							.WEN1_1({GND,GND}), 
							.Almost_Empty_0(Almost_Empty0),
							.Almost_Empty_1(Almost_Empty1), 
							.Almost_Full_0(Almost_Full0), 
							.Almost_Full_1(Almost_Full1),
							.POP_FLAG_0(POP_FLAG0), 
							.POP_FLAG_1(POP_FLAG1), 
							.PUSH_FLAG_0(PUSH_FLAG0), 
							.PUSH_FLAG_1(PUSH_FLAG1),
							.RD_0(out_reg0[17:0]), 
							.RD_1(out_reg1[17:0]),
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

if (Concatenation_En == 1'b1)
	
	ram8k_2x1_cell_macro U2 (.A1_0(addr_wr) , 
							.A1_1(addr_wr), 
							.A2_0(addr_rd), 
							.A2_1(addr_rd), 
							.ASYNC_FLUSH_0(Async_Flush0), 
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
							.DIR_0(Fifo0_Dir),
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
							.WD_1(in_reg0[35:18]), 
							.WD_0(in_reg0[17:0]), 
							.WIDTH_SELECT1_0(WS1_0), 
							.WIDTH_SELECT1_1({GND,GND}), 
							.WIDTH_SELECT2_0(WS2_0),
							.WIDTH_SELECT2_1({GND,GND}), 
							.WEN1_0({GND,GND}), 
							.WEN1_1({GND,GND}), 
							.Almost_Empty_0(Almost_Empty0),
							.Almost_Empty_1(), 
							.Almost_Full_0(Almost_Full0), 
							.Almost_Full_1(),
							.POP_FLAG_0(POP_FLAG0), 
							.POP_FLAG_1(), 
							.PUSH_FLAG_0(PUSH_FLAG0), 
							.PUSH_FLAG_1(),
							.RD_0(out_reg0[17:0]), 
							.RD_1(out_reg0[35:18]),
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

endgenerate
						
generate

if(wr_width_int0 == rd_width_int0)
	assign DOUT0[rd_width_int0 -1 :0]= out_reg0[rd_width_int0 -1 :0];
else if(wr_depth_int0 == depth_level2 && wr_width_int0 > 9)
begin
	if(rd_width_int0 >18)
	begin
		assign DOUT0[rd_width_int0 -1: by0_2_read]=out_reg0[35- zero0_18_2_rg:18];
		assign DOUT0[by0_2_read-1 : 0]= out_reg0[17-zero0_18_2_rg: 0];
    end
	else if(rd_width_int0 <=9)
		assign DOUT0[rd_width_int0 - 1:0]= out_reg0[rd_width_int0-1:0];
	else 
	begin
		assign DOUT0[rd_width_int0 -1 : by0_2_read] = out_reg0[17-zero0_9_2_rg:9];
		assign DOUT0[by0_2_read-1:0]=out_reg0[8-zero0_9_2_rg:0];	
	end
end	
else if(wr_depth_int0 ==depth_level2 && wr_width_int0 <=9 )
begin
	assign DOUT0[rd_width_int0 -1 : by0_2_read] = out_reg0[17-zero0_9_2_rg:9];
	assign DOUT0[by0_2_read-1:0]=out_reg0[8-zero0_9_2_rg:0];	
end
else if(wr_depth_int0 == depth_level3) 
begin
	if(rd_depth_int0 == depth_level1)
	begin
		assign DOUT0[rd_width_int0 -1 :by0_4_readx3 ]= out_reg0[35-zero0_9_2_rg:27];
		assign DOUT0[by0_4_readx3-1: by0_4_readx2]=out_reg0[26-zero0_9_2_rg:18];
		assign DOUT0[by0_4_readx2-1: by0_4_read]=out_reg0[17-zero0_9_2_rg:9];
		assign DOUT0[by0_4_read-1: 0]=out_reg0[8-zero0_9_2_rg:0];
	end	
	else
		begin
		assign DOUT0[rd_width_int0 -1 : by0_2_read] = out_reg0[17-zero0_9_2_rg:9];
		assign DOUT0[by0_2_read-1:0]=out_reg0[8-zero0_9_2_rg:0];	
	end
end
else                  
	assign DOUT0[rd_width_int0-1:0] = out_reg0[rd_width_int0-1:0];

if (Concatenation_En == 1'b0) begin	
	if(wr_width_int1 == rd_width_int1)
		assign DOUT1[rd_width_int1 -1 :0]= out_reg1[rd_width_int1 -1 :0];
	else if(wr_depth_int1 ==depth_level2 && wr_width_int1 <=9 )
	begin
		assign DOUT1[rd_width_int1 -1 : by1_2_read] = out_reg1[17-zero1_9_2_rg:9];
		assign DOUT1[by1_2_read-1:0]=out_reg1[8-zero1_9_2_rg:0];	
	end
	else                  
		assign DOUT1[rd_width_int1-1:0] = out_reg1[rd_width_int1-1:0];
end

endgenerate	

endmodule
