module RAM_16K_BLK (WA0,RA0,WD0,WD0_SEL,RD0_SEL,WClk0,RClk0,WClk0_En,RClk0_En,WEN0,RD0,
					WA1,RA1,WD1,WD1_SEL,RD1_SEL,WClk1,RClk1,WClk1_En,RClk1_En,WEN1,RD1,
					LS,DS,SD,LS_RB1,DS_RB1,SD_RB1);

parameter 	Concatenation_En = 0,

			wr_addr_int0 	= 9,
	 	    rd_addr_int0 	= 9,
	  		wr_depth_int0 	= 512,
	  		rd_depth_int0 	= 512,
	  		wr_width_int0 	= 36,
	  		rd_width_int0 	= 36,
            wr_enable_int0 	= 4,
	  		reg_rd_int0 	= 0,
			
			wr_addr_int1 = 9,
	 	    rd_addr_int1 = 9,
	  		wr_depth_int1 = 512,
	  		rd_depth_int1 = 512,
	  		wr_width_int1 = 18,
	  		rd_width_int1 = 18,
            wr_enable_int1 = 2,
	  		reg_rd_int1 = 0;
			
input [wr_addr_int0-1:0] WA0;
input [rd_addr_int0-1:0] RA0;
input WD0_SEL,RD0_SEL;
input WClk0,RClk0;
input WClk0_En,RClk0_En;
input [wr_enable_int0-1:0] WEN0;
input [wr_width_int0-1:0] WD0;
output [rd_width_int0-1:0] RD0;

input [wr_addr_int1-1:0] WA1;
input [rd_addr_int1-1:0] RA1;
input WD1_SEL,RD1_SEL;
input WClk1,RClk1;
input WClk1_En,RClk1_En;
input [wr_enable_int1-1:0] WEN1;
input [wr_width_int1-1:0] WD1;
output [rd_width_int1-1:0] RD1;

input LS,DS,SD,LS_RB1,DS_RB1,SD_RB1;

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
parameter zero1_36_2_odd =(36-wr_width_int1+1)/2;
parameter zero1_18_2_odd = (18-wr_width_int1+1)/2;
parameter zero1_36_4_1 =(36-wr_width_int1+1)/4;
parameter zero1_36_4_2 =(36-wr_width_int1+2)/4;
parameter zero1_36_4_3=(36-wr_width_int1+3)/4;
parameter zero1_36_4 = (36- wr_width_int1) /4 ;
parameter zero1_18_2 =(18-wr_width_int1)/2;
parameter by1_2 = (wr_width_int1)/2;
parameter by1_4 = (wr_width_int1)/4;
parameter by1_4_2 = (wr_width_int1/4)*2;
parameter by1_4_3 =(wr_width_int1/4)*3;
parameter zero1_9_2_rg = 9-wr_width_int1;
parameter by1_2_read = (rd_width_int1)/2;

assign VCC = 1'b1;
assign GND = 1'b0;

wire WClk0_Sel,RClk0_Sel;
wire WClk1_Sel,RClk1_Sel;

wire 		reg_rd0;
wire 		reg_rd1;
wire [10:0] addr_wr0,addr_rd0,addr_wr1,addr_rd1;

wire [35:0] in_reg0;
wire [35:0] in_reg1;

wire [4:0] wen_reg0;
wire [2:0] wen_reg1;

wire [35:0] out_reg0;
wire [17:0] out_reg1;

wire [1:0] WS1_0,WS2_0; 
wire [1:0] WS1_1,WS2_1;
wire [1:0] WS_GND;

assign WClk0_Sel = 1'b0;
assign RClk0_Sel = 1'b0;

assign WClk1_Sel = 1'b0;
assign RClk1_Sel = 1'b0;

assign reg_rd0 =reg_rd_int0;
assign WS_GND = 2'b00;

assign reg_rd1 =reg_rd_int1;

assign wen_reg0[4:wr_enable_int0]=0;
assign wen_reg0[wr_enable_int0-1:0]=WEN0;

assign wen_reg1[2:wr_enable_int1]=0;
assign wen_reg1[wr_enable_int1-1:0]=WEN1;

generate

if(wr_addr_int0 == 11)
	begin
	assign addr_wr0[10:0]=WA0;
	end
else
	begin
	assign addr_wr0[10:wr_addr_int0]=0;
	assign addr_wr0[wr_addr_int0-1:0]=WA0;
	end
	
if(rd_addr_int0 == 11)
	begin
	assign addr_rd0[10:0]=RA0;
	end
else
	begin
	assign addr_rd0[10:rd_addr_int0]=0;
	assign addr_rd0[rd_addr_int0-1:0]=RA0;
	end	
	
if (Concatenation_En == 1'b1) begin
	assign addr_wr1=11'b0000000000;
	assign addr_rd1=11'b0000000000;
end

if (Concatenation_En == 1'b0) begin
	if(wr_addr_int1 == 11)
	begin
		assign addr_wr1[10:0]=WA1;
	end
	else
	begin
		assign addr_wr1[10:wr_addr_int1]=0;
		assign addr_wr1[wr_addr_int1-1:0]=WA1;
	end
	
	if(rd_addr_int1 == 11)
	begin
		assign addr_rd1[10:0]=RA1;
	end
	else
	begin
		assign addr_rd1[10:rd_addr_int1]=0;
		assign addr_rd1[rd_addr_int1-1:0]=RA1;
	end
end	

if(wr_width_int0 == 1)
begin
	assign in_reg0[35:wr_width_int0]=0;
	assign in_reg0[0]=WD0[0];
end
else if (wr_width_int0 ==36 || wr_width_int0 == 18 || wr_width_int0 ==9)
   begin
	assign in_reg0[35:wr_width_int0]=0;
	assign in_reg0[wr_width_int0-1:0]=WD0;
end
else if(wr_width_int0 ==35 || (wr_width_int0 ==17 && wr_depth_int0 ==1024) ||(wr_width_int0==17 && wr_depth_int0 ==512 && rd_depth_int0 != 2048) || (wr_width_int0==8&&wr_depth_int0==2048) || (wr_width_int0 ==8 && wr_depth_int0 ==1024 && rd_depth_int0 != 2048))
begin
	assign in_reg0[35:wr_width_int0]=0;				 
	assign in_reg0[wr_width_int0-1 :0]=WD0;
end
else if(wr_width_int0 == rd_width_int0)
begin
	assign in_reg0[35:wr_width_int0]=0;
	assign in_reg0[wr_width_int0 -1 :0]=WD0;
end
else if(wr_width_int0 ==34 && rd_depth_int0 ==2048 ) 
begin
	assign in_reg0[35]=0;
	assign in_reg0[26]=0;
	assign in_reg0[34:27]=WD0[33:26];
	assign in_reg0[25:18]=WD0[25:18];
	assign in_reg0[17:0]=WD0[17:0];
end
else if(wr_width_int0 ==33 && rd_depth_int0 == 2048 )
begin
	assign in_reg0[35]=0;
	assign in_reg0[26]=0;
	assign in_reg0[17]=0;
	assign in_reg0[34:27]=WD0[33:26];
	assign in_reg0[25:18]=WD0[25:18];
	assign in_reg0[16:0]=WD0[17:0];
end
else if(wr_depth_int0 == 512)
begin
	if(rd_depth_int0 == 1024)
	begin
		if(wr_width_int0 > 18)
		begin
			if(mod2_0 ==0)
        	begin
				assign in_reg0[17 : 18-zero0_36_2]=0;
				assign in_reg0[35 :  36-zero0_36_2]=0  ;            
                assign in_reg0[18-zero0_36_2-1:0]=WD0[by0_2-1:0] ;
                assign in_reg0[36-zero0_36_2-1:18]= WD0[wr_width_int0-1:by0_2];
            end
			else
			begin
				assign in_reg0[35:36-zero0_36_2_odd]=0;
				assign in_reg0[17:18-zero0_36_2_odd+1]=0;
				assign in_reg0[36-zero0_36_2_odd-1:18]=WD0[wr_width_int0-1:by0_2+1];
				assign in_reg0[18-zero0_36_2_odd:0]=WD0[by0_2:0];
			end
		end
		else
		begin
			if(mod2_0==0)
			begin
				assign in_reg0[8:9-zero0_18_2]=0;
				assign in_reg0[17: 18-zero0_18_2]=0;
				assign in_reg0[9-zero0_18_2-1:0]=WD0[by0_2-1:0];
				assign in_reg0[18-zero0_18_2:9]=WD0[wr_width_int0-1:by0_2];
			end
			else
			begin
				assign in_reg0[17:18-zero0_18_2_odd]=0;
				assign in_reg0[8:9-zero0_18_2_odd+1]=0;
				assign in_reg0[18-zero0_18_2_odd-1:9]=WD0[wr_width_int0-1:by0_2+1];
				assign in_reg0[9-zero0_18_2_odd:0]=WD0[by0_2:0];
			end
		end
	end
	else if(rd_depth_int0 == 2048 )
	begin
		if(mod4_0 == 0)
		begin
			assign in_reg0[35:36-zero0_36_4] = 0;
			assign in_reg0[26:27- zero0_36_4]=0;
			assign in_reg0[17:18-zero0_36_4]=0;
			assign in_reg0[8:9-zero0_36_4]=0;
			assign in_reg0[36-zero0_36_4-1:27]=WD0[wr_width_int0-1:by0_4_3];
			assign in_reg0[27-zero0_36_4-1:18]= WD0[by0_4_3-1:by0_4_2];
			assign in_reg0[18-zero0_36_4-1:9]=WD0[by0_4_2-1:by0_4];
			assign in_reg0[9-zero0_36_4-1:0]=WD0[by0_4-1:0];
		end
		else if (mod4_0==1)
		begin
			assign in_reg0[35:36-zero0_36_4_3]=0;
			assign in_reg0[26:27-zero0_36_4_3]=0;
			assign in_reg0[17:18-zero0_36_4_3]=0;
			assign in_reg0[8:9-zero0_36_4_3+1]=0;
			assign in_reg0[36-zero0_36_4_3-1:27]=WD0[wr_width_int0-1:by0_4_3+1];
			assign in_reg0[27-zero0_36_4_3-1:18]=WD0[by0_4_3:by0_4_2+1];
			assign in_reg0[18-zero0_36_4_3-1:9]=WD0[by0_4_2:by0_4+1];
			assign in_reg0[9-zero0_36_4_3:0]=WD0[by0_4:0];
		end
		else if (mod4_0==2)
		begin
			assign in_reg0[35:36-zero0_36_4_2]=0;
			assign in_reg0[26:27-zero0_36_4_2]=0;
			assign in_reg0[17:18-zero0_36_4_2+1]=0;
			assign in_reg0[8:9-zero0_36_4_2+1]=0;
			assign in_reg0[36-zero0_36_4_2-1:27]=WD0[wr_width_int0-1:by0_4_3+2];
			assign in_reg0[27-zero0_36_4_2-1:18]=WD0[by0_4_3+1:by0_4_2+2];
			assign in_reg0[18-zero0_36_4_2:9]=WD0[by0_4_2+1:by0_4+1];
			assign in_reg0[9-zero0_36_4_2:0]=WD0[by0_4:0];
		end
		else if (mod4_0==3)
		begin
			assign in_reg0[35:36-zero0_36_4_1-1]=0;
			assign in_reg0[26:27-zero0_36_4_1]=0;
			assign in_reg0[17:18-zero0_36_4_1]=0;
			assign in_reg0[8:9-zero0_36_4_1]=0;
			assign in_reg0[36-zero0_36_4_1-2:27]=WD0[wr_width_int0-1:by0_4_3+3];
			assign in_reg0[27-zero0_36_4_1-1:18]=WD0[by0_4_3+2:by0_4_2+2];
			assign in_reg0[18-zero0_36_4_1-1:9]=WD0[by0_4_2+1:by0_4+1];
			assign in_reg0[9-zero0_36_4_1-1:0]=WD0[by0_4:0];
	    end
	end
end
else if(wr_depth_int0 == 1024)
begin
	if(rd_depth_int0 == 2048)
	begin
		if(mod2_0==0)
		begin
			assign in_reg0[8:9-zero0_18_2]=0;
			assign in_reg0[17: 18-zero0_18_2]=0;
			assign in_reg0[9-zero0_18_2-1:0]=WD0[ by0_2-1:0];
			assign in_reg0[18-zero0_18_2:9]=WD0[wr_width_int0-1:by0_2];
		end
		else
		begin
			assign in_reg0[17:18-zero0_18_2_odd]=0;
			assign in_reg0[8:9-zero0_18_2_odd+1]=0;
			assign in_reg0[18-zero0_18_2_odd-1:9]=WD0[wr_width_int0-1:by0_2+1];
			assign in_reg0[9-zero0_18_2_odd:0]=WD0[by0_2:0];
		end
	end
	else
	begin
		assign in_reg0[35:wr_width_int0]=0;
		assign in_reg0[wr_width_int0-1:0]=WD0;
	end
end
else
begin 
	assign in_reg0[35:wr_width_int0]=0;
	assign in_reg0[wr_width_int0-1:0]=WD0;	
end	

if (Concatenation_En == 1'b0) begin
	if(wr_width_int1 == 1)
	begin
		assign in_reg1[35:wr_width_int1]=0;
		assign in_reg1[0]=WD1[0];
	end
	else if (wr_width_int1 ==36 || wr_width_int1 == 18 || wr_width_int1 ==9)
	begin
		assign in_reg1[35:wr_width_int1]=0;
		assign in_reg1[wr_width_int1-1:0]=WD1;
	end
	else if(wr_width_int1 ==35 || (wr_width_int1 ==17 && wr_depth_int1 ==1024) ||(wr_width_int1==17 && wr_depth_int1 ==512 && rd_depth_int1 != 2048) || (wr_width_int1==8&&wr_depth_int1==2048) || (wr_width_int1 ==8 && wr_depth_int1 ==1024 && rd_depth_int1 != 2048))
	begin
		assign in_reg1[35:wr_width_int1]=0;				 
		assign in_reg1[wr_width_int1-1 :0]=WD1;
	end
	else if(wr_width_int1 == rd_width_int1)
	begin
		assign in_reg1[35:wr_width_int1]=0;
		assign in_reg1[wr_width_int1 -1 :0]=WD1;
	end
	else if(wr_width_int1 ==34 && rd_depth_int1 ==2048 ) 
	begin
		assign in_reg1[35]=0;
		assign in_reg1[26]=0;
		assign in_reg1[34:27]=WD1[33:26];
		assign in_reg1[25:18]=WD1[25:18];
		assign in_reg1[17:0]=WD1[17:0];
	end
	else if(wr_width_int1 ==33 && rd_depth_int1 == 2048 )
	begin
		assign in_reg1[35]=0;
		assign in_reg1[26]=0;
		assign in_reg1[17]=0;
		assign in_reg1[34:27]=WD1[33:26];
		assign in_reg1[25:18]=WD1[25:18];
		assign in_reg1[16:0]=WD1[17:0];
	end
	else if(wr_depth_int1 == 512)
	begin
		if(rd_depth_int1 == 1024)
		begin
			if(wr_width_int1 > 18)
			begin
				if(mod2_1 ==0)
				begin
					assign in_reg1[17 : 18-zero1_36_2]=0;
					assign in_reg1[35 :  36-zero1_36_2]=0  ;            
					assign in_reg1[18-zero1_36_2-1:0]=WD1[by1_2-1:0] ;
					assign in_reg1[36-zero1_36_2-1:18]= WD1[wr_width_int1-1:by1_2];
				end
				else
				begin
					assign in_reg1[35:36-zero1_36_2_odd]=0;
					assign in_reg1[17:18-zero1_36_2_odd+1]=0;
					assign in_reg1[36-zero1_36_2_odd-1:18]=WD1[wr_width_int1-1:by1_2+1];
					assign in_reg1[18-zero1_36_2_odd:0]=WD1[by1_2:0];
				end
			end
			else
			begin
				if(mod2_1==0)
				begin
					assign in_reg1[8:9-zero1_18_2]=0;
					assign in_reg1[17: 18-zero1_18_2]=0;
					assign in_reg1[9-zero1_18_2-1:0]=WD1[by1_2-1:0];
					assign in_reg1[18-zero1_18_2:9]=WD1[wr_width_int1-1:by1_2];
				end
				else
				begin
					assign in_reg1[17:18-zero1_18_2_odd]=0;
					assign in_reg1[8:9-zero1_18_2_odd+1]=0;
					assign in_reg1[18-zero1_18_2_odd-1:9]=WD1[wr_width_int1-1:by1_2+1];
					assign in_reg1[9-zero1_18_2_odd:0]=WD1[by1_2:0];
				end
			end
		end
		else if(rd_depth_int1 == 2048 )
		begin
			if(mod4_1 == 0)
			begin
				assign in_reg1[35:36-zero1_36_4] = 0;
				assign in_reg1[26:27- zero1_36_4]=0;
				assign in_reg1[17:18-zero1_36_4]=0;
				assign in_reg1[8:9-zero1_36_4]=0;
				assign in_reg1[36-zero1_36_4-1:27]=WD1[wr_width_int1-1:by1_4_3];
				assign in_reg1[27-zero1_36_4-1:18]= WD1[by1_4_3-1:by1_4_2];
				assign in_reg1[18-zero1_36_4-1:9]=WD1[by1_4_2-1:by1_4];
				assign in_reg1[9-zero1_36_4-1:0]=WD1[by1_4-1:0];
			end
			else if (mod4_1==1)
			begin
				assign in_reg1[35:36-zero1_36_4_3]=0;
				assign in_reg1[26:27-zero1_36_4_3]=0;
				assign in_reg1[17:18-zero1_36_4_3]=0;
				assign in_reg1[8:9-zero1_36_4_3+1]=0;
				assign in_reg1[36-zero1_36_4_3-1:27]=WD1[wr_width_int1-1:by1_4_3+1];
				assign in_reg1[27-zero1_36_4_3-1:18]=WD1[by1_4_3:by1_4_2+1];
				assign in_reg1[18-zero1_36_4_3-1:9]=WD1[by1_4_2:by1_4+1];
				assign in_reg1[9-zero1_36_4_3:0]=WD1[by1_4:0];
			end
			else if (mod4_1==2)
			begin
				assign in_reg1[35:36-zero1_36_4_2]=0;
				assign in_reg1[26:27-zero1_36_4_2]=0;
				assign in_reg1[17:18-zero1_36_4_2+1]=0;
				assign in_reg1[8:9-zero1_36_4_2+1]=0;
				assign in_reg1[36-zero1_36_4_2-1:27]=WD1[wr_width_int1-1:by1_4_3+2];
				assign in_reg1[27-zero1_36_4_2-1:18]=WD1[by1_4_3+1:by1_4_2+2];
				assign in_reg1[18-zero1_36_4_2:9]=WD1[by1_4_2+1:by1_4+1];
				assign in_reg1[9-zero1_36_4_2:0]=WD1[by1_4:0];
			end
			else if (mod4_1==3)
			begin
				assign in_reg1[35:36-zero1_36_4_1-1]=0;
				assign in_reg1[26:27-zero1_36_4_1]=0;
				assign in_reg1[17:18-zero1_36_4_1]=0;
				assign in_reg1[8:9-zero1_36_4_1]=0;
				assign in_reg1[36-zero1_36_4_1-2:27]=WD1[wr_width_int1-1:by1_4_3+3];
				assign in_reg1[27-zero1_36_4_1-1:18]=WD1[by1_4_3+2:by1_4_2+2];
				assign in_reg1[18-zero1_36_4_1-1:9]=WD1[by1_4_2+1:by1_4+1];
				assign in_reg1[9-zero1_36_4_1-1:0]=WD1[by1_4:0];
			end
		end
	end
	else if(wr_depth_int1 == 1024)
	begin
		if(rd_depth_int1 == 2048)
		begin
			if(mod2_1==0)
			begin
				assign in_reg1[8:9-zero1_18_2]=0;
				assign in_reg1[17: 18-zero1_18_2]=0;
				assign in_reg1[9-zero1_18_2-1:0]=WD1[ by1_2-1:0];
				assign in_reg1[18-zero1_18_2:9]=WD1[wr_width_int1-1:by1_2];
			end
			else
			begin
				assign in_reg1[17:18-zero1_18_2_odd]=0;
				assign in_reg1[8:9-zero1_18_2_odd+1]=0;
				assign in_reg1[18-zero1_18_2_odd-1:9]=WD1[wr_width_int1-1:by1_2+1];
				assign in_reg1[9-zero1_18_2_odd:0]=WD1[by1_2:0];
			end
		end
		else
		begin
			assign in_reg1[35:wr_width_int1]=0;
			assign in_reg1[wr_width_int1-1:0]=WD1;
		end
	end
	else
	begin 
		assign in_reg1[35:wr_width_int1]=0;
		assign in_reg1[wr_width_int1-1:0]=WD1;	
	end	
end

if(rd_depth_int0 == 2048 && wr_depth_int0 ==512)
	assign WS1_0 =2'b10;
else if(rd_depth_int0 == 2048 && wr_depth_int0 == 1024)
	assign WS1_0=2'b01;
else if(wr_depth_int0 == 512 && wr_width_int0 <=9)
	assign WS1_0=2'b01;
else if(wr_width_int0 <=9)
	assign WS1_0 = 2'b00;
else if(wr_width_int0 >9 && wr_width_int0 <=18)
	assign WS1_0 = 2'b01;
else if(wr_width_int0 > 18)
	assign WS1_0 = 2'b10;
	
if(wr_depth_int0 == 2048 && rd_depth_int0 == 512)
	assign WS2_0 = 2'b10;
else if(wr_depth_int0 == 2048  && rd_depth_int0 == 1024)
	assign WS2_0 = 2'b01;
else if(rd_depth_int0 == 512 && rd_width_int0 <=9)
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

	ram8k_2x1_cell_macro U1 (.A1_0(addr_wr0) , 
							.A1_1(addr_wr1), 
							.A2_0(addr_rd0), 
							.A2_1(addr_rd1), 
							.ASYNC_FLUSH_0(GND), //chk
							.ASYNC_FLUSH_1(GND), //chk
							.ASYNC_FLUSH_S0(GND),
							.ASYNC_FLUSH_S1(GND),
							.CLK1_0(WClk0), 
							.CLK1_1(WClk1), 
							.CLK1S_0(WClk0_Sel), 
							.CLK1S_1(WClk1_Sel),
							.CLK1EN_0(WClk0_En), 
							.CLK1EN_1(WClk1_En), 
							.CLK2_0(RClk0),
							.CLK2_1(RClk1), 
							.CLK2S_0(RClk0_Sel),
							.CLK2S_1(RClk1_Sel), 
							.CLK2EN_0(RClk0_En), 
							.CLK2EN_1(RClk1_En), 
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
							.P1_0(GND), //P1_0
							.P1_1(GND), //P1_1
							.P2_0(GND), //
							.P2_1(GND), //
							.PIPELINE_RD_0(reg_rd0), 
							.PIPELINE_RD_1(reg_rd1), 
							.SYNC_FIFO_0(GND),
							.SYNC_FIFO_1(GND), 
							.WD_1(in_reg1[17:0]), 
							.WD_0(in_reg0[17:0]), 
							.WIDTH_SELECT1_0(WS1_0), 
							.WIDTH_SELECT1_1(WS1_1), 
							.WIDTH_SELECT2_0(WS2_0),
							.WIDTH_SELECT2_1(WS2_1), 
							.WEN1_0(wen_reg0[1:0]), 
							.WEN1_1(wen_reg1[1:0]), 
							.Almost_Empty_0(),
							.Almost_Empty_1(), 
							.Almost_Full_0(), 
							.Almost_Full_1(),
							.POP_FLAG_0(), 
							.POP_FLAG_1(), 
							.PUSH_FLAG_0(), 
							.PUSH_FLAG_1(),
							.RD_0(out_reg0[17:0]), 
							.RD_1(out_reg1),
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

	ram8k_2x1_cell_macro U2 (.A1_0(addr_wr0) , 
							.A1_1(addr_wr1), 
							.A2_0(addr_rd0), 
							.A2_1(addr_rd1), 
							.ASYNC_FLUSH_0(GND), 
							.ASYNC_FLUSH_1(GND),
							.ASYNC_FLUSH_S0(GND),
							.ASYNC_FLUSH_S1(GND),
							.CLK1_0(WClk0), 
							.CLK1_1(WClk0),
							.CLK1S_0(WClk0_Sel),
							.CLK1S_1(WClk0_Sel), 
							.CLK1EN_0(WClk0_En), 
							.CLK1EN_1(WClk0_En), 
							.CLK2_0(RClk0),
							.CLK2_1(RClk0),
							.CLK2S_0(RClk0_Sel),
							.CLK2S_1(RClk0_Sel), 
							.CLK2EN_0(RClk0_En), 
							.CLK2EN_1(RClk0_En), 
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
							.WD_1(in_reg0[35:18]), 
							.WD_0(in_reg0[17:0]), 
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
	assign RD0[rd_width_int0 -1 :0]= out_reg0[rd_width_int0 -1 :0];
else if(wr_depth_int0 == 1024 && wr_width_int0 > 9)
begin
	if(rd_width_int0 >18)
	begin
		assign RD0[rd_width_int0 -1: by0_2_read]=out_reg0[35- zero0_18_2_rg:18];
		assign RD0[by0_2_read-1 : 0]= out_reg0[17-zero0_18_2_rg: 0];
    end
	else if(rd_width_int0 <=9)
		assign RD0[rd_width_int0 - 1:0]=out_reg0[rd_width_int0-1:0];
	else 
	begin
		assign RD0[rd_width_int0 -1 : by0_2_read] = out_reg0[17-zero0_9_2_rg:9];
		assign RD0[by0_2_read-1:0]=out_reg0[8-zero0_9_2_rg:0];	
	end
end	
else if(wr_depth_int0 ==1024 && wr_width_int0 <=9 )
begin
	assign RD0[rd_width_int0 -1 : by0_2_read] = out_reg0[17-zero0_9_2_rg:9];
	assign RD0[by0_2_read-1:0]=out_reg0[8-zero0_9_2_rg:0];	
end
else if(wr_depth_int0 == 2048) 
begin
	if(rd_depth_int0 == 512)
	begin
		assign RD0[rd_width_int0 -1 :by0_4_readx3 ]= out_reg0[35-zero0_9_2_rg:27];
		assign RD0[by0_4_readx3-1: by0_4_readx2]=out_reg0[26-zero0_9_2_rg:18];
		assign RD0[by0_4_readx2-1: by0_4_read]=out_reg0[17-zero0_9_2_rg:9];
		assign RD0[by0_4_read-1: 0]=out_reg0[8-zero0_9_2_rg:0];
	end	
	else
		begin
		assign RD0[rd_width_int0 -1 : by0_2_read] = out_reg0[17-zero0_9_2_rg:9];
		assign RD0[by0_2_read-1:0]=out_reg0[8-zero0_9_2_rg:0];	
	end
end
else                  
	assign RD0[rd_width_int0-1:0] = out_reg0[rd_width_int0-1:0];
	
if (Concatenation_En == 1'b0) begin
	if(wr_width_int1 == rd_width_int1)
		assign RD1[rd_width_int1 -1 :0]= out_reg1[rd_width_int1 -1 :0];
	else if(wr_depth_int1 ==1024 && wr_width_int1 <=9 )
	begin
		assign RD1[rd_width_int1 -1 : by1_2_read] = out_reg1[17-zero1_9_2_rg:9];
		assign RD1[by1_2_read-1:0]=out_reg1[8-zero1_9_2_rg:0];	
	end
	else                  
		assign RD1[rd_width_int1-1:0] = out_reg1[rd_width_int1-1:0];
end
	
endgenerate							

endmodule


