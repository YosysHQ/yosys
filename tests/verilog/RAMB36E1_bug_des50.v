module dual_port_ram(clk, we1, we2, addr1, addr2, data1, data2, out1, out2);
parameter ADDR_WIDTH = 13;
parameter DATA_WIDTH = 32;
input clk;
input we1, we2;
input [ADDR_WIDTH-1:0] addr1, addr2;
input [DATA_WIDTH-1:0] data1, data2;
output reg [DATA_WIDTH-1:0] out1, out2;
reg [DATA_WIDTH-1:0] RAM [(1<<ADDR_WIDTH)-1:0];
always @(posedge clk)
begin
    if (we1)
            RAM[addr1] <= data1;
    if (we2)
            RAM[addr2] <= data2;
    out1 <= RAM[addr1];
    out2 <= RAM[addr2];
end
endmodule

////dual_port_ram module
//(* keep_hierarchy *)
//(* ram_block *)
//module dual_port_ram #(
//    parameter ADDR_WIDTH = 13,
//    parameter DATA_WIDTH = 32
//) (
//    input clk,
//
//    input [ADDR_WIDTH-1:0] addr1,
//    input [ADDR_WIDTH-1:0] addr2,
//    input [DATA_WIDTH-1:0] data1,
//    input [DATA_WIDTH-1:0] data2,
//    input we1,
//    input we2,
//    output reg [DATA_WIDTH-1:0] out1,
//    output reg [DATA_WIDTH-1:0] out2
//);
//
//    localparam MEM_DEPTH = 2 ** ADDR_WIDTH;
//    (* RAM_STYLE="BLOCK" *)
//    reg [DATA_WIDTH-1:0] myBlockram [MEM_DEPTH-1:0];
//  //  reg [DATA_WIDTH-1:0] ram_data_a = {DATA_WIDTH{1'b0}};
//  //  reg [DATA_WIDTH-1:0] ram_data_b = {DATA_WIDTH{1'b0}};
//
//    always@(posedge clk) begin //Port 1
//        if(we1) begin
//            myBlockram[addr1] = data1;
//        end
//        out1 = myBlockram[addr1]; //New data read-during write behaviour (blocking assignments)
//    end
//
//    always@(posedge clk) begin //Port 2
//        if(we2) begin
//            myBlockram[addr2] = data2;
//        end
//        out2 = myBlockram[addr2]; //New data read-during write behaviour (blocking assignments)
//    end
//
//endmodule // dual_port_ram

// A FIFO is used for a non-duplex communication between a processor and another

module fifo(clk,resetn,dataIn,dataOut,wr,rd,full,empty,overflow);
  parameter LOGSIZE = 2; //Default size is 4 elements (only 3 reqd)
  parameter WIDTH   = 32; //Default width is 32 bits
  parameter SIZE = 1 << LOGSIZE;

  input clk,resetn,rd,wr;
  input [WIDTH-1:0] dataIn;
  output[WIDTH-1:0] dataOut;

  output full,empty,overflow;

  reg [WIDTH-1:0] fifo[SIZE-1:0] ; //Fifo data stored here
  reg overflow; //true if WR but no room, cleared on RD
  reg [LOGSIZE-1:0] wptr,rptr; //Fifo read and write pointers
  wire [WIDTH-1:0] fifoWire[SIZE-1:0] ; //Fifo data stored here

  reg counter = 0;
  reg [WIDTH-1:0] tempOut;

  wire [LOGSIZE-1:0] wptr_inc = wptr+1;
  assign empty = (wptr==rptr);
  assign full  = (wptr_inc==rptr);
  assign dataOut = tempOut;

  //assign fifoWire[0] = fifo[0];

  //always @ (posedge clk) begin
  //  if(reset) begin
  //    wptr<=0;
  //    rptr<=0;
      
  //    fifo[0] <= 32'hdeadbeef;
  //	  fifo[1] <= 32'hdeadbeef;
  //	  fifo[2] <= 32'hdeadbeef;      
  //  end
  //end

  always @ (posedge clk) begin
    if(wr==1) begin
      fifo[wptr]<=dataIn;
      wptr <= wptr + 1;
    end
    if(rd==1&&!empty) begin
      casex(counter)
        0: begin
		  tempOut <= fifo[rptr];
		  rptr <= rptr + 1;
		  counter <= 1;
		end
	  endcase
	end
	
	if(rd==0) begin
	  counter <=0;	        
    end  
    if(resetn==0) begin
      rptr<=0;
      wptr<=0;
    end    
  end  

endmodule



/****************************************************************************
          Generic Register
****************************************************************************/
module lo_reg(d,clk,resetn,en,q);
parameter WIDTH=32;

input clk;
input resetn;
input en;
input [WIDTH-1:0] d;
output [WIDTH-1:0] q;
reg [WIDTH-1:0] q;

always @(posedge clk or negedge resetn)		//asynchronous reset
begin
	if (resetn==0)
		q<=0;
	else if (en==1)
		q<=d;
end

endmodule


/****************************************************************************
          Generic Register
****************************************************************************/
module hi_reg(d,clk,resetn,en,q);
parameter WIDTH=32;

input clk;
input resetn;
input en;
input [WIDTH-1:0] d;
output [WIDTH-1:0] q;
reg [WIDTH-1:0] q;

always @(posedge clk or negedge resetn)		//asynchronous reset
begin
	if (resetn==0)
		q<=0;
	else if (en==1)
		q<=d;
end

endmodule

module branchresolve ( en, rs, rt, eq, ne, ltz, lez, gtz, gez, eqz);
parameter WIDTH=32; //Deepak : Change from parameter to define
input en;
input [WIDTH-1:0] rs;
input [WIDTH-1:0] rt;
output eq;
output ne;
output ltz;
output lez;
output gtz;
output gez;
output eqz;

assign eq=(en)&(rs==rt);
assign ne=(en)&~eq;
assign eqz=(en)&~(|rs);
assign ltz=(en)&rs[WIDTH-1];
assign lez=(en)&rs[WIDTH-1] | eqz;
assign gtz=(en)&(~rs[WIDTH-1]) & ~eqz;
assign gez=(en)&(~rs[WIDTH-1]);

endmodule

module signext16 ( in, out);

input [15:0] in;
output [31:0] out;

assign out={{16{in[15]}},in[15:0]};

endmodule

module merge26lo(in1, in2, out);
input [31:0] in1;
input [25:0] in2;
output [31:0] out;

assign out[31:0]={in1[31:28],in2[25:0],2'b0};
endmodule


/****************************************************************************
          Register File

   - Has two read ports (a and b) and one write port (c)
   - sel chooses the register to be read/written
****************************************************************************/
module reg_file(clk,resetn, 
	a_reg, a_readdataout, a_en,
	b_reg, b_readdataout, b_en,
	c_reg, c_writedatain, c_we);

parameter WIDTH=32;
parameter NUMREGS=32;
parameter LOG2NUMREGS=5;

input clk;
input resetn;

input a_en;
input b_en;

input [LOG2NUMREGS-1:0] a_reg,b_reg,c_reg;
output [WIDTH-1:0] a_readdataout, b_readdataout;
input [WIDTH-1:0] c_writedatain;
input c_we;

wire [WIDTH-1:0] discard_read_data_a, discard_read_data_b;

	dual_port_ram	#(.ADDR_WIDTH(LOG2NUMREGS), .DATA_WIDTH(WIDTH)) reg_file1 (
				.clk (clk),
				.we1 (c_we&(|c_reg)),
				.we2 (c_we&(|c_reg)),
				.addr1 (c_reg[LOG2NUMREGS-1:0]),
				.addr2 (a_reg[LOG2NUMREGS-1:0]),
				.data1 (c_writedatain),
				.data2 (c_writedatain),
				.out1 (a_readdataout),
				.out2 (discard_read_data_a)
    );

    dual_port_ram #(.ADDR_WIDTH(LOG2NUMREGS), .DATA_WIDTH(WIDTH))	reg_file2 (
				.clk (clk),
				.we1 (c_we&(|c_reg)),
				.we2 (c_we&(|c_reg)),
				.addr1 (c_reg[LOG2NUMREGS-1:0]),
				.addr2 (b_reg[LOG2NUMREGS-1:0]),
				.data1 (c_writedatain),
				.data2 (c_writedatain),
				.out1 (b_readdataout),
				.out2 (discard_read_data_b)
    );

endmodule




module pcadder(pc, offset, result);
parameter PC_WIDTH=32;

input [PC_WIDTH-1:0] pc;
input [PC_WIDTH-1:0] offset;
output [PC_WIDTH-1:0] result;

wire dum;

assign {dum,result} = pc + {offset[PC_WIDTH-3:0],2'b0};

endmodule

module register_1bit(
	d,
	clk,
	resetn,
	en,
	q
);

//parameter WIDTH=32;

input clk;
input resetn;
input en;
input  d;
output q;
reg q;

always @(posedge clk )		
begin
	if (resetn==0)
		q<=0;
	else if (en==1)
		q<=d;
end

endmodule


/******************************************************************************
            Data memory and interface

Operation table:

  load/store sign size1 size0    |   Operation
7     0       1     1     1      |      LB
5     0       1     0     1      |      LH
0     0       X     0     0      |      LW
3     0       0     1     1      |      LBU
1     0       0     0     1      |      LHU
11    1       X     1     1      |      SB
9     1       X     0     1      |      SH
8     1       X     0     0      |      SW

******************************************************************************/

module data_mem( clk, resetn, en, stalled,
                d_writedata,
                d_address,
                boot_daddr, boot_ddata, boot_dwe, 
                op,
                d_loadresult);

parameter D_ADDRESSWIDTH=32;

parameter DM_DATAWIDTH=32;
parameter DM_BYTEENAWIDTH=4;            // usually should be DM_DATAWIDTH/8
//parameter DM_ADDRESSWIDTH=16;         //Deepak commented
//parameter DM_SIZE=16384;              //Deepak commented

//Deepak : UnCommented to see why the processor is stopping after the first instruction
parameter DM_ADDRESSWIDTH=8;     //Deepak
parameter DM_SIZE=64;          //Deepak : Increased the size of memory

input clk;
input resetn;
input en;
output stalled;

input [31:0] boot_daddr;
input [31:0] boot_ddata;
input boot_dwe;

input [D_ADDRESSWIDTH-1:0] d_address;
input [4-1:0] op;
input [DM_DATAWIDTH-1:0] d_writedata;
output [DM_DATAWIDTH-1:0] d_loadresult;

wire [DM_BYTEENAWIDTH-1:0] d_byteena;
wire [DM_DATAWIDTH-1:0] d_readdatain;
wire [DM_DATAWIDTH-1:0] d_writedatamem;
wire d_write;
wire [1:0] d_address_latched;

assign d_write=op[3];
//assign d_write = d_write;//deepak
register d_address_reg(d_address[1:0],clk,1'b1,en,d_address_latched);
    defparam d_address_reg.WIDTH=2;
                
store_data_translator sdtrans_inst(
    .write_data(d_writedata),
    .d_address(d_address[1:0]),
    .store_size(op[1:0]),
    .d_byteena(d_byteena),
    .d_writedataout(d_writedatamem));

load_data_translator ldtrans_inst(
    .d_readdatain(d_readdatain),
    .d_address(d_address_latched[1:0]),
    .load_size(op[1:0]),
    .load_sign_ext(op[2]),
    .d_loadresult(d_loadresult));
  
// 1 cycle stall state machine
onecyclestall staller(en&~d_write,clk,resetn,stalled);


endmodule



/****************************************************************************
          Store data translator
          - moves store data to appropriate byte/halfword 
          - interfaces with altera blockrams
****************************************************************************/
module store_data_translator(
    write_data,             // data in least significant position
    d_address,
    store_size,
    d_byteena,
    d_writedataout);        // shifted data to coincide with address
parameter WIDTH=32;

input [WIDTH-1:0] write_data;
input [1:0] d_address;
input [1:0] store_size;
output [3:0] d_byteena;
output [WIDTH-1:0] d_writedataout;

reg [3:0] d_byteena;
reg [WIDTH-1:0] d_writedataout;

always @(write_data or d_address or store_size)
begin
  
    case (store_size)
        2'b11:
            case(d_address[1:0])
                0: 
                begin 
                    d_byteena=4'b1000; 
                    d_writedataout={write_data[7:0],24'b0}; 
                end
                1: 
                begin 
                    d_byteena=4'b0100; 
                    d_writedataout={8'b0,write_data[7:0],16'b0}; 
                end
                2: 
                begin 
                    d_byteena=4'b0010; 
                    d_writedataout={16'b0,write_data[7:0],8'b0}; 
                end
                default: 
                begin 
                    d_byteena=4'b0001; 
                    d_writedataout={24'b0,write_data[7:0]}; 
                end
            endcase
        2'b01:
            case(d_address[1])
                0: 
                begin 
                    d_byteena=4'b1100; 
                    d_writedataout={write_data[15:0],16'b0}; 
                end
                default: 
                begin 
                    d_byteena=4'b0011; 
                    d_writedataout={16'b0,write_data[15:0]}; 
                end
            endcase
        default:
        begin
            d_byteena=4'b1111;
            d_writedataout=write_data;
        end
    endcase
end

endmodule

/****************************************************************************
          Load data translator
          - moves read data to appropriate byte/halfword and zero/sign extends
****************************************************************************/
module load_data_translator(
    d_readdatain,
    d_address,
    load_size,
    load_sign_ext,
    d_loadresult);
parameter WIDTH=32;

input [WIDTH-1:0] d_readdatain;
input [1:0] d_address;
input [1:0] load_size;
input load_sign_ext;
output [WIDTH-1:0] d_loadresult;

reg [WIDTH-1:0] d_loadresult;

always @(d_readdatain or d_address or load_size or load_sign_ext)
begin
    case (load_size)
        2'b11:
        begin
            case (d_address[1:0])
                0: d_loadresult[7:0]=d_readdatain[31:24];
                1: d_loadresult[7:0]=d_readdatain[23:16];
                2: d_loadresult[7:0]=d_readdatain[15:8];
                default: d_loadresult[7:0]=d_readdatain[7:0];
            endcase
            d_loadresult[31:8]={24{load_sign_ext&d_loadresult[7]}};
        end
        2'b01:
        begin
            case (d_address[1])
                0: d_loadresult[15:0]=d_readdatain[31:16];
                default: d_loadresult[15:0]=d_readdatain[15:0];
            endcase
            d_loadresult[31:16]={16{load_sign_ext&d_loadresult[15]}};
        end
        default:
            d_loadresult=d_readdatain;
    endcase
end

endmodule

/****************************************************************************
			Fetch Unit
op
  0  Conditional PC write
  1  UnConditional PC write

****************************************************************************/

module ifetch(
	clk,
	resetn,
	boot_iaddr, 
	boot_idata, 
	boot_iwe,
	load,
	load_data,
	op,
	we,
	squashn,
	en,
	pc_out,
	instr,
	opcode,
	func,
	rs,
	rt,
	rd,
	instr_index,
	offset,
	sa,
	next_pc
);

parameter PC_WIDTH=30;
parameter I_DATAWIDTH=32;
parameter I_ADDRESSWIDTH=8;
parameter I_SIZE=64;

input [31:0] boot_iaddr;
input [31:0] boot_idata;
input boot_iwe;

input clk;
input resetn;
input en;     // PC increment enable
input we;     // PC write enable
input squashn;// squash fetch
input op;     // determines if conditional or unconditional branch
input load;
input [I_DATAWIDTH-1:0] load_data;
output [I_DATAWIDTH-1:0] pc_out;   // output pc + 1 shifted left 2 bits
output [PC_WIDTH-1:0] next_pc;
output [31:26] opcode;
output [25:21] rs;
output [20:16] rt;
output [15:11] rd;
output [10:6] sa;
output [15:0] offset;
output [25:0] instr_index;
output [5:0] func;
output [I_DATAWIDTH-1:0] instr;


wire [PC_WIDTH-1:0] pc_plus_1;
wire [PC_WIDTH-1:0] pc;
assign pc_plus_1 = pc;
wire ctrl_load;
wire out_of_sync;

assign ctrl_load=(load&~op|op);
wire notresetn;
assign notresetn = ~resetn;
wire count_en;
assign count_en = (~ctrl_load)&~out_of_sync;
wire counter_en;
assign counter_en = en | we;
wire [32:2] reg_load_data;

assign reg_load_data = load_data [31:2];

wire reg_d;
wire reg_en;
assign reg_d = (we&(~en)&(squashn));
assign reg_en = en|we;


register_1bit sync_pcs_up( reg_d, clk, resetn,reg_en, out_of_sync);

wire wren1;
assign wren1 = 1'b0;
wire [9:0] next_pc_wire;
assign next_pc_wire = next_pc [9:0];

wire [31:0]dummyout2;

// aryap: removed for benchmark graph generatio
dual_port_ram #(.ADDR_WIDTH(10), .DATA_WIDTH(32)) imem_replace(
	.clk (clk),
	.we1(wren1),
	.we2(boot_iwe),
	.data1(load_data),
	.data2(boot_idata),
	.out1(instr),
	.out2(dummyout2),
	.addr1(next_pc_wire),
	.addr2(boot_iaddr[9:0])
);

wire [31:0] dummyin1;
assign dummyin1 = 32'b00000000000000000000000000000000;

dummy_counter pc_reg ((reg_load_data),(clk),(counter_en),(count_en),(notresetn),(ctrl_load),(pc));
assign pc_out [31:2] = pc_plus_1;
assign pc_out [1:0] = 2'b00;

assign next_pc = ctrl_load ? load_data[31:2] : pc_plus_1;
assign opcode=instr[31:26];
assign rs=instr[25:21];
assign rt=instr[20:16];
assign rd=instr[15:11];
assign sa=instr[10:6];
assign offset=instr[15:0]; 
assign instr_index=instr[25:0];
assign func=instr[5:0];

//Odin II does not recognize that boot_iaddr 
//is being used to write data when system 
//is given 1'b1 on the boot_iwe wire so is
//is assigned to an unused wire which is 
//later dropped by the optimizer.
wire NoUse;
assign NoUse = ( |boot_iaddr );

endmodule


module dummy_counter (
	data,
	clock,
	clk_en,
	cnt_en,
	aset,
	sload,
	q
);

parameter PC_WIDTH=30;


input [31:2] data;
input clock;
input clk_en;
input cnt_en;
input aset;
input sload;
output [PC_WIDTH-1:0] q;
reg [PC_WIDTH-1:0] q;

wire [2:0] sload_cnten_aset;
assign sload_cnten_aset [0] = sload;
assign sload_cnten_aset [1] = cnt_en;
assign sload_cnten_aset [2] = aset;

always @ (posedge clock)

//if (cnt_en == 1)
//q <= q+1;
begin

case (sload_cnten_aset)
	3'b000:
		q <= q;
	3'b011:
		q <= q;
	3'b110:
		q <= q;
	3'b111:
		q <= q;
	3'b101:
		q <= q;
	3'b100: 
		q <= data;
	3'b010:
	begin
		if (clk_en) 
			q <= q+1;
		else
			q <= q;
		end
	3'b001:
		q <= 29'b00000000000000000000000000000;
	default:
		q <= q;
endcase
end
endmodule


/****************************************************************************
		  MUL/DIV unit

Operation table

   op sign dir
4  1   0    x    |  MULTU
6  1   1    x    |  MULT
0  0   0    0    |  ShiftLeft
1  0   0    1    |  ShiftRightLogic
3  0   1    1    |  ShiftRightArith
****************************************************************************/
module mul(
	clk,
	resetn,
	sa,
	dst, 
	opB,
	opA,
	op, 
	start, 
	stalled,
	shift_result,
	lo,
	hi
);

input clk;
input resetn;

input start;
output stalled;

input [4:0] dst;

input [31:0] opA;
input [31:0] opB;
input [4:0] sa;
input [2:0] op;

output [31:0] shift_result;
output [31:0] hi;
output [31:0] lo;

/********* Control Signals *********/
wire is_signed;
wire dir;
wire is_mul;
assign is_mul=op[2];      // selects between opB and the computed shift amount
assign is_signed=op[1];
assign dir=op[0];         // selects between 2^sa and 2^(32-sa) for right shift

/********* Circuit Body *********/
wire dum;
wire dum2; 
wire dum3;
wire [32:0] opB_mux_out;
wire [4:0] left_sa;     // Amount of left shift required for both left/right
reg [32:0] decoded_sa;
wire [31:0] result;
//assign opB_mux_out= (is_mul) ? {is_signed&opB[31],opB} : decoded_sa;
assign opB_mux_out = opB;



dummy_mult fake_mult_one (opA,opB_mux_out, clk, resetn, result);
assign hi = result [15:8];
assign lo = result [7:0];
// Cannot support this now
/*
lpm_mult  lpm_mult_component (
  .dataa ({is_signed&opA[31],opA}),
  .datab (opB_mux_out),
  .sum(),
  .clock(clk),
  .clken(),
  .aclr(~resetn),
  .result ({dum2,dum,hi,lo}));
defparam
  lpm_mult_component.lpm_32a = 32+1,
  lpm_mult_component.lpm_32b = 32+1,
  lpm_mult_component.lpm_32p = 2*32+2,
  lpm_mult_component.lpm_32s = 1,
  lpm_mult_component.lpm_pipeline = 1,
  lpm_mult_component.lpm_type = "LPM_MULT",
  lpm_mult_component.lpm_representation = "SIGNED",
  lpm_mult_component.lpm_hint = "MAXIMIZE_SPEED=6";
*/
assign shift_result= (dir & |sa) ? hi : lo;


// 1 cycle stall state machine
wire or_dst;
wire start_and_ismul;
wire request;

assign or_dst = |dst;
assign start_and_ismul = start & is_mul; 
assign request = (or_dst & start & ~is_mul) | (start_and_ismul);
onecyclestall staller(request,clk,resetn,stalled);


endmodule

module dummy_mult  (
	opA,
	opB_mux_out, 
	clk, 
	resetn, 
	result
);

input [31:0] opA;
input [31:0] opB_mux_out;
input  clk;
input  resetn;
output[31:0] result;
reg [31:0] result;


always @ (posedge clk)
begin
	if (resetn)
		result <= 32'b00000000000000000000000000000000;
	else
		//multiplier by star symbol
		//though this is probably supposed to be signed
		result <= opA * opB_mux_out;
end
endmodule


/****************************************************************************
          Shifter unit

Opcode Table:

sign_ext dir 
 0        0    |  ShiftLeft
 0        1    |  ShiftRightLogic
 1        1    |  ShiftRightArith
          
****************************************************************************/
module shifter(clk, resetn,
            opB, sa, 
            op, start, stalled,
            dst,
            result);
parameter WIDTH=32;

input clk;
input resetn;

input [WIDTH-1:0] opB;
input [4:0] sa;                             // Shift Amount
input [2-1:0] op;

input start;
output stalled;

input [4:0] dst;

output [WIDTH-1:0] result;

wire sign_ext;
wire shift_direction;
assign sign_ext=op[1];
assign shift_direction=op[0];

reg [WIDTH-1:0] shifter;
reg shift_state;
reg [4:0] shift_count;
wire wasjustbusy;
wire is_zeroshift;
wire was_zeroshift;
wire is_nop;

wire hi_bit, lo_bit;

assign hi_bit=sign_ext&opB[WIDTH-1];
assign lo_bit=0;
// to separate nops from zero shifts (which occur) we hack this
assign is_nop=~(|dst);
assign is_zeroshift=(~|sa)&~is_nop;

assign stalled = (start&(~wasjustbusy)&~is_nop&~was_zeroshift)|shift_state;
assign result=shifter;

register wasjustbusy_reg(shift_state,clk,resetn,1'b1,wasjustbusy);
  defparam wasjustbusy_reg.WIDTH=1;

register was_zeroshift_reg(is_zeroshift&~was_zeroshift,
                           clk,resetn,start,was_zeroshift);
  defparam was_zeroshift_reg.WIDTH=1;

always @(posedge clk or negedge resetn)
begin
    if (!resetn)
    begin
        shifter<=0;
        shift_state<=0;
        shift_count<=0;
    end
    else
    begin
        case(shift_state)
            0:
                if (start&~wasjustbusy)
                begin
                    shift_count<=sa;
                    shifter<=opB;
                    if (!is_zeroshift && !is_nop)
                        shift_state<=1;
                end
            default:
            begin
                if (shift_count==1)
                    shift_state<=0;
                shift_count<=shift_count-1;
                shifter[31]<=(shift_direction) ? hi_bit : shifter[30];
                shifter[30]<=(shift_direction) ? shifter[31] : shifter[29];
                shifter[29]<=(shift_direction) ? shifter[30] : shifter[28];
                shifter[28]<=(shift_direction) ? shifter[29] : shifter[27];
                shifter[27]<=(shift_direction) ? shifter[28] : shifter[26];
                shifter[26]<=(shift_direction) ? shifter[27] : shifter[25];
                shifter[25]<=(shift_direction) ? shifter[26] : shifter[24];
                shifter[24]<=(shift_direction) ? shifter[25] : shifter[23];
                shifter[23]<=(shift_direction) ? shifter[24] : shifter[22];
                shifter[22]<=(shift_direction) ? shifter[23] : shifter[21];
                shifter[21]<=(shift_direction) ? shifter[22] : shifter[20];
                shifter[20]<=(shift_direction) ? shifter[21] : shifter[19];
                shifter[19]<=(shift_direction) ? shifter[20] : shifter[18];
                shifter[18]<=(shift_direction) ? shifter[19] : shifter[17];
                shifter[17]<=(shift_direction) ? shifter[18] : shifter[16];
                shifter[16]<=(shift_direction) ? shifter[17] : shifter[15];
                shifter[15]<=(shift_direction) ? shifter[16] : shifter[14];
                shifter[14]<=(shift_direction) ? shifter[15] : shifter[13];
                shifter[13]<=(shift_direction) ? shifter[14] : shifter[12];
                shifter[12]<=(shift_direction) ? shifter[13] : shifter[11];
                shifter[11]<=(shift_direction) ? shifter[12] : shifter[10];
                shifter[10]<=(shift_direction) ? shifter[11] : shifter[9];
                shifter[9]<=(shift_direction) ? shifter[10] : shifter[8];
                shifter[8]<=(shift_direction) ? shifter[9] : shifter[7];
                shifter[7]<=(shift_direction) ? shifter[8] : shifter[6];
                shifter[6]<=(shift_direction) ? shifter[7] : shifter[5];
                shifter[5]<=(shift_direction) ? shifter[6] : shifter[4];
                shifter[4]<=(shift_direction) ? shifter[5] : shifter[3];
                shifter[3]<=(shift_direction) ? shifter[4] : shifter[2];
                shifter[2]<=(shift_direction) ? shifter[3] : shifter[1];
                shifter[1]<=(shift_direction) ? shifter[2] : shifter[0];
                shifter[0]<=(shift_direction) ? shifter[1] : lo_bit;
            end
        endcase
    end
end

endmodule

/****************************************************************************
          logic unit
- note ALU must be able to increment PC for JAL type instructions

Operation Table
  op
  0     AND
  1     OR
  2     XOR
  3     NOR
****************************************************************************/
module logic_unit (
            opA, opB,
            op,
            result);
parameter WIDTH=32;


input [WIDTH-1:0] opA;
input [WIDTH-1:0] opB;
input [2-1:0] op;
output [WIDTH-1:0] result;

reg [WIDTH-1:0] logic_result;

always@(opA or opB or op )
    case(op)
        2'b00:
            logic_result=opA&opB;
        2'b01:
            logic_result=opA|opB;
        2'b10:
            logic_result=opA^opB;
        2'b11:
            logic_result=~(opA|opB);
    endcase

assign result=logic_result;


endmodule


// Dummy Adder, to replace Altera IP
// Take from VTR Benchmarks

module full_adder (cin,x,y,s,cout);
input cin;
input x;
input y;
output s;
output cout;
assign s = x^y^cin;
assign cout = (x&y) | (x & cin) | (y&cin);
endmodule

module dummy_add_sub (
	dataa,
	datab,
	cin,
	result
);

//this is goign to be UUUUGGGGGGLLLYYYYY
//probably going to do some serious timing violations
// but i'm sure it will be interesting for the packing problem
input [31:0] dataa;
input [31:0] datab;
input cin;
output [32:0] result;
//
wire [31:0] carry_from;
wire [31:0] sum;


full_adder bit0 (cin,dataa[0],datab[0],sum[0],carry_from [0]);
full_adder bit1 (carry_from [0],dataa[1],datab[1],sum[1],carry_from [1]);
full_adder bit2 (carry_from [1],dataa[2],datab[2],sum[2],carry_from [2]);
full_adder bit3 (carry_from [2],dataa[3],datab[3],sum[3],carry_from [3]);
full_adder bit4 (carry_from [3],dataa[4],datab[4],sum[4],carry_from [4]);
full_adder bit5 (carry_from [4],dataa[5],datab[5],sum[5],carry_from [5]);
full_adder bit6 (carry_from [5],dataa[6],datab[6],sum[6],carry_from [6]);
full_adder bit7 (carry_from [6],dataa[7],datab[7],sum[7],carry_from [7]);

full_adder bit8 (carry_from [7],dataa[8],datab[8],sum[8],carry_from [8]);
full_adder bit9 (carry_from [8],dataa[9],datab[9],sum[9],carry_from [9]);
full_adder bit10 (carry_from [9],dataa[10],datab[10],sum[10],carry_from [10]);
full_adder bit11 (carry_from [10],dataa[11],datab[11],sum[11],carry_from [11]);
full_adder bit12 (carry_from [11],dataa[12],datab[12],sum[12],carry_from [12]);
full_adder bit13 (carry_from [12],dataa[13],datab[13],sum[13],carry_from [13]);
full_adder bit14 (carry_from [13],dataa[14],datab[14],sum[14],carry_from [14]);
full_adder bit15 (carry_from [14],dataa[15],datab[15],sum[15],carry_from [15]);

full_adder bit16 (carry_from [15],dataa[16],datab[16],sum[16],carry_from [16]);
full_adder bit17 (carry_from [16],dataa[17],datab[17],sum[17],carry_from [17]);
full_adder bit18 (carry_from [17],dataa[18],datab[18],sum[18],carry_from [18]);
full_adder bit19 (carry_from [18],dataa[19],datab[19],sum[19],carry_from [19]);
full_adder bit20 (carry_from [19],dataa[20],datab[20],sum[20],carry_from [20]);
full_adder bit21 (carry_from [20],dataa[21],datab[21],sum[21],carry_from [21]);
full_adder bit22 (carry_from [21],dataa[22],datab[22],sum[22],carry_from [22]);
full_adder bit23 (carry_from [22],dataa[23],datab[23],sum[23],carry_from [23]);

full_adder bit24 (carry_from [23],dataa[24],datab[24],sum[24],carry_from [24]);
full_adder bit25 (carry_from [24],dataa[25],datab[25],sum[25],carry_from [25]);
full_adder bit26 (carry_from [25],dataa[26],datab[26],sum[26],carry_from [26]);
full_adder bit27 (carry_from [26],dataa[27],datab[27],sum[27],carry_from [27]);
full_adder bit28 (carry_from [27],dataa[28],datab[28],sum[28],carry_from [28]);
full_adder bit29 (carry_from [28],dataa[29],datab[29],sum[29],carry_from [29]);
full_adder bit30 (carry_from [29],dataa[30],datab[30],sum[30],carry_from [30]);
full_adder bit31 (carry_from [30],dataa[31],datab[31],sum[31],carry_from [31]);

assign result [31:0] = sum;
assign result [32] = carry_from [31];

endmodule

/****************************************************************************
          Generic Register
****************************************************************************/
module register(d,clk,resetn,en,q);
parameter WIDTH=32;

input clk;
input resetn;
input en;
input [WIDTH-1:0] d;
output [WIDTH-1:0] q;
reg [WIDTH-1:0] q;

always @(posedge clk or negedge resetn)		//asynchronous reset
begin
	if (resetn==0)
		q<=0;
	else if (en==1)
		q<=d;
end

endmodule

/****************************************************************************
          Generic Register - synchronous reset
****************************************************************************/
module register_sync(d,clk,resetn,en,q);
parameter WIDTH=32;

input clk;
input resetn;
input en;
input [WIDTH-1:0] d;
output [WIDTH-1:0] q;
reg [WIDTH-1:0] q;

always @(posedge clk)		//synchronous reset
begin
	if (resetn==0)
		q<=0;
	else if (en==1)
		q<=d;
end

endmodule

/****************************************************************************
          Generic Pipelined Register

          - Special component, components starting with "pipereg" have
          their enables treated independently of instructrions that use them.
          - They are enabled whenever the stage is active and not stalled
****************************************************************************/
module pipereg(d,clk,resetn,en,squashn,q);
parameter WIDTH=32;

input clk;
input resetn;
input en;
input squashn;
input [WIDTH-1:0] d;
output [WIDTH-1:0] q;
reg [WIDTH-1:0] q;

always @(posedge clk)   //synchronous reset
begin
  if (resetn==0 || squashn==0)
    q<=0;
  else if (en==1)
    q<=d;
end

endmodule

/****************************************************************************
          Generic Pipelined Register 2 -OLD: If not enabled, queues squash

          - This piperegister stalls the reset signal as well
module pipereg_full(d,clk,resetn,squashn,en,q);
parameter WIDTH=32;

input clk;
input resetn;
input en;
input squashn;
input [WIDTH-1:0] d;
output [WIDTH-1:0] q;
reg [WIDTH-1:0] q;
reg squash_save;

  always @(posedge clk)   //synchronous reset
  begin
    if (resetn==0 || (squashn==0 && en==1) || (squash_save&en))
      q<=0;
    else if (en==1)
      q<=d;
  end

  always @(posedge clk)
  begin
    if (resetn==1 && squashn==0 && en==0)
      squash_save<=1;
    else
      squash_save<=0;
  end
endmodule
****************************************************************************/

/****************************************************************************
          One cycle Stall circuit
****************************************************************************/
module onecyclestall(request,clk,resetn,stalled);
input request;
input clk;
input resetn;
output stalled;

  reg T,Tnext;

  // State machine for Stalling 1 cycle
  always@(request or T)
  begin
    case(T) 
      1'b0: Tnext=request;
      1'b1: Tnext=0;
    endcase 
  end       
  always@(posedge clk)
    if (~resetn)
      T<=0; 
    else    
      T<=Tnext;
  assign stalled=(request&~T);
endmodule

/****************************************************************************
          Multi cycle Stall circuit - with wait signal

          - One FF plus one 2:1 mux to stall 1st cycle on request, then wait
          - this makes wait don't care for the first cycle
****************************************************************************/
module multicyclestall(request, devwait,clk,resetn,stalled);
input request;
input devwait;
input clk;
input resetn;
output stalled;

  reg T;

  always@(posedge clk)
    if (~resetn)
      T<=0;
    else
      T<=stalled;

  assign stalled=(T) ? devwait : request;
endmodule
                
/****************************************************************************
          One cycle - Pipeline delay register
****************************************************************************/
module pipedelayreg(d,en,clk,resetn,squashn,dst,stalled,q);
parameter WIDTH=32;
input [WIDTH-1:0] d;
input [4:0] dst;
input en;
input clk;
input resetn;
input squashn;
output stalled;
output [WIDTH-1:0] q;

  reg [WIDTH-1:0] q;
  reg T,Tnext;

  // State machine for Stalling 1 cycle
  always@(en or T or dst)
  begin
    case(T) 
      0: Tnext=en&(|dst);
      1: Tnext=0;
    endcase 
  end       
  always@(posedge clk)
    if (~resetn)
      T<=0; 
    else    
      T<=Tnext;

  always @(posedge clk)   //synchronous reset
  begin
    if (resetn==0 || squashn==0)
      q<=0;
    else if (en==1)
      q<=d;
  end

  assign stalled=(en&~T&(|dst));
endmodule

/****************************************************************************
          Fake Delay
****************************************************************************/
module fakedelay(d,clk,q);
parameter WIDTH=32;
input [WIDTH-1:0] d;
input clk;
output [WIDTH-1:0] q;

assign q=d;

endmodule

/****************************************************************************
          Zeroer
****************************************************************************/
module zeroer(d,en,q);
parameter WIDTH=32;

input en;
input [WIDTH-1:0] d;
output [WIDTH-1:0] q;
assign q= (en) ? d : 0;

endmodule

/****************************************************************************
          NOP - used to hack position of multiplexors
****************************************************************************/
module nop(d,q);
parameter WIDTH=32;

input [WIDTH-1:0] d;
output [WIDTH-1:0] q;

  assign q=d;

endmodule

/****************************************************************************
          Const
****************************************************************************/
//Deepak : Changed const to constant to resolve compilation error
module constant (out);

parameter WIDTH=32;
parameter VAL=31;

output [WIDTH-1:0] out;

assign out=VAL;

endmodule

/****************************************************************************
          Branch detector
****************************************************************************/
module branch_detector(opcode, func, is_branch);
input [5:0] opcode;
input [5:0] func;
output is_branch;

wire is_special;

assign is_special=!(|opcode);
assign is_branch=((!(|opcode[5:3])) && !is_special) || 
                  ((is_special)&&(func[5:3]==3'b001));

endmodule


/****************************************************************************
		  AddSub unit
- Should perform ADD, ADDU, SUBU, SUB, SLT, SLTU

  is_slt signext addsub
	op[2] op[1] op[0]  |  Operation
0     0     0     0         SUBU
2     0     1     0         SUB
1     0     0     1         ADDU
3     0     1     1         ADD
4     1     0     0         SLTU
6     1     1     0         SLT

****************************************************************************/
module addersub (
	opB, 
	opA,
	op, 
	result_slt,
	result 
);

//parameter WIDTH=32;
//`DEFINE WIDTH 32


input [31:0] opA;
input [31:0] opB;
//input carry_in;
input [2:0] op;
output result_slt;
output [31:0] result;



wire [32:0] sum;


wire addsub;
wire useless;
assign useless = op[1] & op[2];


assign addsub=op[0];
wire not_addsub;
assign not_addsub = ~addsub;

assign result=sum[31:0];

assign result_slt=sum[32];

dummy_add_sub adder32bit (opA,opB,not_addsub,sum);


// This is an LPM from Altera, replacing with a dummy one for now
/*
lpm_add_sub adder_inst(
	.dataa({signext&opA[WIDTH-1],opA}),
	.datab({signext&opB[WIDTH-1],opB}),
	.cin(~addsub),
	.add_sub(addsub),
	.result(sum)
		// synopsys translate_off
		,
		.cout (),
		.clken (),
		.clock (),
		.overflow (),
		.aclr ()
		// synopsys translate_on
	);
//defparam 
//    adder_inst.lpm_width=WIDTH+1,
//   adder_inst.lpm_representation="SIGNED";
*/

endmodule



//Deepak: Commeted due to error: Module cannot be declared more than once

//`include "lo_reg.v"
//`include "hi_reg.v"
//`include "data_mem_stall.v"
//`include "mul.v"
//`include "shifter_perbit_pipe.v"
//`include "logic_unit.v"
//`include "addersub_slt.v"
//`include "merge26lo.v"
//`include "branchresolve.v"
//`include "pcadder.v"
//`include "signext16.v"
//`include "reg_file_pipe.v"
//`include "ifetch_pipe.v"
//`include "components.v"

/*To remove an instruction and the associated logic, comment the specific `defines*/
/*Instruction Set and Processor Logic Optimization Block*/
`define ADDI
`define ADDIU
`define ANDI
`define SPECIAL 
`define REGIMM       
`define J            
`define JAL          
`define BEQ          
`define BNE          
`define BLEZ         
`define BGTZ         
`define ADDI         
`define ADDIU        
`define SLTI         
`define SLTIU        
`define ANDI         
`define ORI          
`define XORI         
`define LUI          
`define LB           
`define LH           
`define LWL          
`define LW           
`define LBU          
`define LHU          
`define LWR          
`define SB           
`define SH           
`define SWL          
`define SW           
`define SWR          
/****** FUNCTION CLASS - bits 5...0 *******/
`define SLL        
`define SRL       
`define SRA       
`define SLLV      
`define SRLV      
`define SRAV      
`define JR        
`define JALR      
`define MFHI      
`define MTHI      
`define MFLO      
`define MTLO      
`define MULT      
`define MULTU     
`define ADD        
`define ADDU       
`define SUB        
`define SUBU       
`define AND        
`define OR         
`define XOR        
`define NOR        
`define SLT        
`define SLTU       
`define BLTZ     
`define BGEZ     
/*End of Instruction Set and Processor Logic Optimization Block*/

module system ( 
	clk,
	resetn,
	boot_iaddr,
	boot_idata,
	boot_iwe,
	boot_daddr,
	boot_ddata,
	boot_dwe,
	reg_file_b_readdataout,
	
	dataInNorth,dataOutNorth,wrNorth,rdNorth,fullNorth,emptyNorth,overflowNorth,
	dataInSouth,dataOutSouth,wrSouth,rdSouth,fullSouth,emptySouth,overflowSouth,
	dataInWest,dataOutWest,wrWest,rdWest,fullWest,emptyWest,overflowWest,
	dataInEast,dataOutEast,wrEast,rdEast,fullEast,emptyEast,overflowEast,
	wrGeneric,genericDataOut);	//FIFO Signals
	
/************************* IO Declarations *********************/
/****************************************************************************
          ISA definitions

  - The MIPS I ISA has a 6 bit opcode in the upper 6 bits.  
  - The opcode can also specify a "class".  There are two classes:
            1.  SPECIAL - look in lowest 6 bits to find operation
            2.  REGIMM - look in [20:16] to find type of branch

****************************************************************************/

/****** OPCODES - bits 31...26 *******/

parameter     OP_SPECIAL      = 6'b000000;
parameter     OP_REGIMM       = 6'b000001;
parameter     OP_J            = 6'b000010;
parameter     OP_JAL          = 6'b000011;
parameter     OP_BEQ          = 6'b000100;
parameter     OP_BNE          = 6'b000101;
parameter     OP_BLEZ         = 6'b000110;
parameter     OP_BGTZ         = 6'b000111;

parameter     OP_ADDI         = 6'b001000;
parameter     OP_ADDIU        = 6'b001001;
parameter     OP_SLTI         = 6'b001010;
parameter     OP_SLTIU        = 6'b001011;
parameter     OP_ANDI         = 6'b001100;
parameter     OP_ORI          = 6'b001101;
parameter     OP_XORI         = 6'b001110;
parameter     OP_LUI          = 6'b001111;

parameter     OP_LB           = 6'b100000;
parameter     OP_LH           = 6'b100001;
parameter     OP_LWL          = 6'b100010;
parameter     OP_LW           = 6'b100011;
parameter     OP_LBU          = 6'b100100;
parameter     OP_LHU          = 6'b100101;
parameter     OP_LWR          = 6'b100110;

parameter     OP_SB           = 6'b101x00;
parameter     OP_SH           = 6'b101x01;
parameter     OP_SWL          = 6'b101010;
parameter     OP_SW           = 6'b101x11;
parameter     OP_SWR          = 6'b101110;

/****** FUNCTION CLASS - bits 5...0 *******/
parameter     FUNC_SLL        = 6'b000000;
parameter     FUNC_SRL        = 6'b000010;
parameter     FUNC_SRA        = 6'b000011;
parameter     FUNC_SLLV       = 6'b000100;
parameter     FUNC_SRLV       = 6'b000110;
parameter     FUNC_SRAV       = 6'b000111;

parameter     FUNC_JR         = 6'b001xx0;
parameter     FUNC_JALR       = 6'b001xx1;

parameter     FUNC_MFHI       = 6'bx10x00;
parameter     FUNC_MTHI       = 6'bx10x01;
parameter     FUNC_MFLO       = 6'bx10x10;
parameter     FUNC_MTLO       = 6'bx10x11;

parameter     FUNC_MULT       = 6'bx11x00;
parameter     FUNC_MULTU      = 6'bx11x01;
parameter     FUNC_DIV        = 6'bx11x10;
parameter     FUNC_DIVU       = 6'bx11x11;

parameter     FUNC_ADD        = 6'b100000;
parameter     FUNC_ADDU       = 6'b100001;
parameter     FUNC_SUB        = 6'b100010;
parameter     FUNC_SUBU       = 6'b100011;
parameter     FUNC_AND        = 6'b100100;
parameter     FUNC_OR         = 6'b100101;
parameter     FUNC_XOR        = 6'b100110;
parameter     FUNC_NOR        = 6'b100111;

parameter     FUNC_SLT        = 6'b101010;
parameter     FUNC_SLTU       = 6'b101011;

/****** REGIMM Class - bits 20...16 *******/
parameter     FUNC_BLTZ       = 1'b0;
parameter     FUNC_BGEZ       = 1'b1;

parameter     OP_COP2       = 6'b010010;
parameter     COP2_FUNC_CFC2     = 6'b111000;
parameter     COP2_FUNC_CTC2     = 6'b111010;
parameter     COP2_FUNC_MTC2     = 6'b111011;

//parameter     FUNC_BLTZAL     = 5'b10000;
//parameter     FUNC_BGEZAL     = 5'b10001;

/****** 
 * Original REGIMM class, compressed above to save decode logic
parameter     FUNC_BLTZ       = 5'b00000;
parameter     FUNC_BGEZ       = 5'b00001;
parameter     FUNC_BLTZAL     = 5'b10000;
parameter     FUNC_BGEZAL     = 5'b10001;
*/

input clk;
input resetn;
input [31:0] boot_iaddr;
input [31:0] boot_idata;
input boot_iwe;
input [31:0] boot_daddr;
input [31:0] boot_ddata;
input boot_dwe;

input  [31:0] dataInNorth;  //FIFO
input  [31:0] dataInSouth;  //FIFO
input  [31:0] dataInWest;  //FIFO
input  [31:0] dataInEast;  //FIFO

output [31:0] dataOutNorth; //FIFO
output [31:0] dataOutSouth; //FIFO
output [31:0] dataOutWest; //FIFO
output [31:0] dataOutEast; //FIFO
output [31:0] genericDataOut; 

output  wrNorth; //FIFO write signal 
output  wrSouth; //FIFO write signal 
output  wrEast; //FIFO write signal 
output  wrWest; //FIFO write signal 
output  wrGeneric;

output  rdNorth; //FIFO write signal 
output  rdSouth; //FIFO write signal 
output  rdEast; //FIFO write signal 
output  rdWest; //FIFO write signal 

input   fullNorth; //FIFO signal which indicates whether FIFO is full or not
input   fullSouth; 
input   fullEast;
input   fullWest;

input   emptyNorth; //FIFO signal which indicates whether FIFO is full or not
input   emptySouth; 
input   emptyEast;
input   emptyWest;

input   overflowNorth; //FIFO signal which indicates whether FIFO has overflowed or not
input   overflowSouth; 
input   overflowEast; 
input   overflowWest; 

output [31:0] reg_file_b_readdataout;


/*********************** Signal Declarations *******************/
wire	branch_mispred;
wire	stall_2nd_delayslot;
wire	has_delayslot;
wire	haz_zeroer0_q_pipereg5_q;
wire	haz_zeroer_q_pipereg5_q;
		// Datapath signals declarations
wire	addersub_result_slt;
wire	[ 31 : 0 ]	addersub_result;
wire	[ 31 : 0 ]	logic_unit_result;
wire	[ 31 : 0 ]	shifter_result;
wire	ctrl_shifter_stalled;
wire	[ 31 : 0 ]	mul_lo;
wire	[ 31 : 0 ]	mul_hi;
wire	[ 31 : 0 ]	ifetch_pc_out;
wire	[ 31 : 0 ]	ifetch_instr;
wire	[ 5 : 0 ]	ifetch_opcode;
wire	[ 5 : 0 ]	ifetch_func;
wire	[ 4 : 0 ]	ifetch_rs;
wire	[ 4 : 0 ]	ifetch_rt;
wire	[ 4 : 0 ]	ifetch_rd;
wire	[ 25 : 0 ]	ifetch_instr_index;
wire	[ 15 : 0 ]	ifetch_offset;
wire	[ 4 : 0 ]	ifetch_sa;
wire	[ 31 : 0 ]	ifetch_next_pc;
wire	[ 31 : 0 ]	data_mem_d_loadresult;
wire	ctrl_data_mem_stalled;
wire	[ 31 : 0 ]	pcadder_result;
wire	[ 31 : 0 ]	signext16_out;
wire	[ 31 : 0 ]	reg_file_b_readdataout;
wire	[ 31 : 0 ]	reg_file_a_readdataout;
wire	[ 31 : 0 ]	merge26lo_out;
wire	branchresolve_eqz;
wire	branchresolve_gez;
wire	branchresolve_gtz;
wire	branchresolve_lez;
wire	branchresolve_ltz;
wire	branchresolve_ne;
wire	branchresolve_eq;
wire	[ 31 : 0 ]	hi_reg_q;
wire	[ 31 : 0 ]	lo_reg_q;
wire	[ 31 : 0 ]	const6_out;
wire	[ 31 : 0 ]	const7_out;
wire	[ 31 : 0 ]	const_out;
wire	[ 31 : 0 ]	pipereg_q;
wire	[ 25 : 0 ]	pipereg1_q;
wire	[ 4 : 0 ]	pipereg2_q;
wire	[ 4 : 0 ]	pipereg5_q;
wire	[ 31 : 0 ]	pipereg3_q;
wire	[ 31 : 0 ]	fakedelay_q;
wire	[ 31 : 0 ]	nop_q;
wire	[ 4 : 0 ]	zeroer_q;
wire	[ 4 : 0 ]	zeroer0_q;
wire	[ 4 : 0 ]	zeroer4_q;
wire	[ 4 : 0 ]	mux3to1_shifter_sa_out;
wire	[ 31 : 0 ]	mux3to1_ifetch_load_data_out;
wire	mux6to1_ifetch_load_out;
wire	[ 31 : 0 ]	mux7to1_reg_file_c_writedatain_out;
wire	[ 31 : 0 ]	mux2to1_addersub_opA_out;
wire	[ 31 : 0 ]	mux2to1_pipereg_d_out;
wire	[ 4 : 0 ]	mux3to1_zeroer4_d_out;
wire	[ 31 : 0 ]	mux3to1_nop_d_out;
wire	[ 5 : 0 ]	pipereg8_q;
wire	[ 5 : 0 ]	pipereg9_q;
wire	[ 4 : 0 ]	pipereg10_q;
/***************** Control Signals ***************/
		//Decoded Opcode signal declarations
reg	[ 1 : 0 ]	ctrl_mux3to1_nop_d_sel;
reg	[ 1 : 0 ]	ctrl_mux3to1_zeroer4_d_sel;
reg	ctrl_mux2to1_pipereg_d_sel;
reg	ctrl_mux2to1_addersub_opA_sel;
reg	ctrl_zeroer0_en;
reg	[ 4 : 0 ]	ctrl_mux7to1_reg_file_c_writedatain_sel; //Deepak Increased select lines
reg	[ 2 : 0 ]	ctrl_mux6to1_ifetch_load_sel;
reg	[ 1 : 0 ]	ctrl_mux3to1_ifetch_load_data_sel;
reg	[ 1 : 0 ]	ctrl_mux3to1_shifter_sa_sel;
reg	ctrl_zeroer4_en;
reg	ctrl_zeroer_en;
reg	[ 2 : 0 ]	ctrl_addersub_op;
reg	ctrl_ifetch_op;
reg	[ 3 : 0 ]	ctrl_data_mem_op;
reg	ctrl_mul_op;
reg	[ 1 : 0 ]	ctrl_logic_unit_op;
reg	[ 1 : 0 ]	ctrl_shifter_op;
		//Enable signal declarations
reg	ctrl_reg_file_c_we;
reg	ctrl_reg_file_b_en;
reg	ctrl_lo_reg_en;
reg	ctrl_branchresolve_en;
reg	ctrl_hi_reg_en;
reg	ctrl_reg_file_a_en;
reg	ctrl_ifetch_we;
reg	ctrl_ifetch_en;
reg	ctrl_data_mem_en;
reg	ctrl_shifter_start;
		//Other Signals
wire	squash_stage2;
wire	stall_out_stage2;
wire	squash_stage1;
wire	stall_out_stage1;
wire	ctrl_pipereg_squashn;
wire	ctrl_pipereg5_squashn;
wire	ctrl_pipereg2_squashn;
wire	ctrl_pipereg3_squashn;
wire	ctrl_pipereg1_squashn;
wire	ctrl_pipereg8_squashn;
wire	ctrl_pipereg9_squashn;
wire	ctrl_pipereg10_squashn;
wire	ctrl_pipereg_resetn;
wire	ctrl_pipereg5_resetn;
wire	ctrl_pipereg2_resetn;
wire	ctrl_pipereg3_resetn;
wire	ctrl_pipereg1_resetn;
wire	ctrl_pipereg8_resetn;
wire	ctrl_pipereg9_resetn;
wire	ctrl_pipereg10_resetn;
wire	ctrl_pipereg_en;
wire	ctrl_pipereg5_en;
wire	ctrl_pipereg2_en;
wire	ctrl_pipereg3_en;
wire	ctrl_pipereg1_en;
wire	ctrl_pipereg8_en;
wire	ctrl_pipereg9_en;
wire	ctrl_pipereg10_en;


wire     [31:0]  tempFifoDataInNorth;
wire     [31:0]  tempFifoDataInSouth;
wire     [31:0]  tempFifoDataInEast;
wire     [31:0]  tempFifoDataInWest;

wire     [31:0]  northEmpty;
wire     [31:0]  southEmpty;
wire     [31:0]  eastEmpty;
wire     [31:0]  westEmpty;

wire     [31:0]  northFull;
wire     [31:0]  southFull;
wire     [31:0]  eastFull;
wire     [31:0]  westFull;

reg writeFifoWest;
reg writeFifoEast;
reg writeFifoNorth;
reg writeFifoSouth;

reg readFifoWest;
reg readFifoEast;
reg readFifoNorth;
reg readFifoSouth;
reg writeGenOut;
reg [31:0] tempDataOutNorth;
reg [31:0] tempDataOutSouth;
reg [31:0] tempDataOutEast;
reg [31:0] tempDataOutWest;
reg [31:0] tempDataOutGeneric;
/*****Parameter Declarations and Port Map*******/

parameter NorthIn  = 32'h00001000;
parameter NorthOut = 32'h00001004;
parameter SouthIn  = 32'h00001008;
parameter SouthOut = 32'h0000100c;
parameter EastIn   = 32'h00001010;
parameter EastOut  = 32'h00001014;
parameter WestIn   = 32'h00001018;
parameter WestOut  = 32'h0000101c;

parameter NorthEmptyPort = 32'h00001020;
parameter NorthFullPort  = 32'h00001024;
parameter SouthEmptyPort = 32'h00001028;
parameter SouthFullPort  = 32'h0000102c;
parameter EastEmptyPort  = 32'h00001030;
parameter EastFullPort   = 32'h00001034;
parameter WestEmptyPort  = 32'h00001038;
parameter WestFullPort   = 32'h0000103c;

parameter genericDataOutPort = 32'h00001200;
/*********Parameter Declartions End************/



assign northFull = 32'h00000000|fullNorth;
assign southFull = 32'h00000000|fullSouth;
assign eastFull  = 32'h00000000|fullEast;
assign westFull  = 32'h00000000|fullWest;

assign northEmpty = 32'h00000000|emptyNorth;
assign southEmpty = 32'h00000000|emptySouth;
assign eastEmpty  = 32'h00000000|emptyEast;
assign westEmpty  = 32'h00000000|emptyWest;



//  Port Map Table
// ****************
// 0x1000 North In
// 0x1004 North Out
// 0x1008 South In
// 0x100c South Out
// 0x1010 East  In
// 0x1014 East  Out
// 0x1018 West  In
// 0x101c West  Out

//Software will check the status of "full" mapped registers before writing.
//That is write as long as  full is not high
//Software will check the status of "empty" mapped registers before read.
//That is read as long as  empty is not high

// 0x1020 NorthEmpty
// 0x1024 NorthFull
// 0x1028 SouthEmpty
// 0x102c SouthFull
// 0x1030 EastEmpty
// 0x1034 EastFull
// 0x1038 WestEmpty
// 0x103c WestFull

/********************Store (Moving data out of the processor **************************/
//assign dataOutWest = (addersub_result==WestOut) ? reg_file_b_readdataout : 32'hxxxxxxxx;
assign dataOutWest = tempDataOutWest;
assign wrWest = writeFifoWest;

//assign dataOutEast = (addersub_result==EastOut) ? reg_file_b_readdataout : 32'hxxxxxxxx;
assign dataOutEast = tempDataOutEast;
assign wrEast = writeFifoEast;

//assign dataOutNorth = (addersub_result==NorthOut) ? reg_file_b_readdataout : 32'hxxxxxxxx;
assign dataOutNorth = tempDataOutNorth;
assign wrNorth = writeFifoNorth;

//assign dataOutSouth = (addersub_result==SouthOut) ? reg_file_b_readdataout : 32'hxxxxxxxx;
assign dataOutSouth = tempDataOutSouth;
assign wrSouth = writeFifoSouth;

//assign genericDataOut = (addersub_result==genericDataOutPort) ? reg_file_b_readdataout : 32'hxxxxxxxx;
assign wrGeneric = writeGenOut;
assign genericDataOut = tempDataOutGeneric;

always@ (posedge clk) begin
	 writeFifoWest   <= (addersub_result==WestOut) ? 1'b1:1'b0;
	 writeFifoEast   <= (addersub_result==EastOut) ? 1'b1:1'b0;
     writeFifoNorth  <= (addersub_result==NorthOut) ? 1'b1:1'b0;
     writeFifoSouth  <= (addersub_result==SouthOut) ? 1'b1:1'b0;
     writeGenOut     <= (addersub_result==genericDataOutPort) ? 1'b1:1'b0;
     
     tempDataOutWest <= (addersub_result==WestOut) ? reg_file_b_readdataout : 32'hxxxxxxxx;
     tempDataOutEast <= (addersub_result==EastOut) ? reg_file_b_readdataout : 32'hxxxxxxxx;
     tempDataOutNorth <= (addersub_result==NorthOut) ? reg_file_b_readdataout : 32'hxxxxxxxx; 
     tempDataOutSouth <= (addersub_result==SouthOut) ? reg_file_b_readdataout : 32'hxxxxxxxx;
     tempDataOutGeneric <= (addersub_result==genericDataOutPort) ? reg_file_b_readdataout : 32'hxxxxxxxx;
     
     //readFifoNorth   <= (addersub_result==NorthIn) ? 1'b1:1'b0;
     //readFifoSouth   <= (addersub_result==SouthIn) ? 1'b1:1'b0;
     //readFifoEast    <= (addersub_result==EastIn)  ? 1'b1:1'b0;
     //readFifoWest    <= (addersub_result==WestIn)  ? 1'b1:1'b0;
     
     //tempFifoDataInEast = (eastEmpty!=32'h00000001) ? dataInEast : 32'hxxxxxxxx;
     //tempFifoDataInWest = (westEmpty!=32'h00000001) ? dataInWest : 32'hxxxxxxxx;
     //tempFifoDataInNorth = (northEmpty!=32'h00000001) ? dataInNorth : 32'hxxxxxxxx;
     //tempFifoDataInSouth = (southEmpty!=32'h00000001) ? dataInSouth : 32'hxxxxxxxx;
end

/********************Load (Taking data into processor from output port*******************/
//If east port has something (indicated by eastEmpty != 1), read data to temp datain east
//assign tempFifoDataInEast = (eastEmpty!=32'h00000001) ? dataInEast : 32'hxxxxxxxx;
assign tempFifoDataInEast = dataInEast;
assign rdEast             = (addersub_result==EastIn) ? 1'b1:1'b0;
//assign rdEast = readFifoEast;

//assign tempFifoDataInWest = (westEmpty!=32'h00000001) ? dataInWest : 32'hxxxxxxxx;
assign tempFifoDataInWest = dataInWest;
assign rdWest             = (addersub_result==WestIn) ? 1'b1:1'b0;
//assign rdWest = readFifoWest;

//assign tempFifoDataInNorth = (northEmpty!=32'h00000001) ? dataInNorth : 32'hxxxxxxxx;
assign tempFifoDataInNorth = dataInNorth;
assign rdNorth             = (addersub_result==NorthIn) ? 1'b1:1'b0;
//assign rdNorth = readFifoNorth;

//assign tempFifoDataInSouth = (southEmpty!=32'h00000001) ? dataInSouth : 32'hxxxxxxxx;
assign tempFifoDataInSouth = dataInSouth;
assign rdSouth             = (addersub_result==SouthIn) ? 1'b1:1'b0;
//assign rdSouth = readFifoSouth;

	


/****************************** Control **************************/

		//Decode Logic for Opcode and Multiplex Select signals
always @(ifetch_opcode or ifetch_func or ifetch_rt)
begin
		// Initialize control opcodes to zero
	ctrl_mux3to1_zeroer4_d_sel = 0;
	ctrl_mux2to1_pipereg_d_sel = 0;
	ctrl_zeroer0_en = 0;
	ctrl_zeroer4_en = 0;
	ctrl_zeroer_en = 0;
	
	casex (ifetch_opcode)
	    `ifdef ADDI
		OP_ADDI: 
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		`ifdef ADDIU		
		OP_ADDIU:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		`ifdef ANDI
		OP_ANDI:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 1;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		`ifdef BEQ
		OP_BEQ:
		begin
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer0_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		`ifdef BGTZ
		OP_BGTZ:
		begin
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer_en = 1;
		end
		`endif
		`ifdef BLEZ
		OP_BLEZ:
		begin
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef BNE
		OP_BNE:
		begin
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer0_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		`ifdef JAL
		OP_JAL:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 0;
			ctrl_zeroer4_en = 1;
		end
		`endif
		
		`ifdef LB
		OP_LB:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef LBU
		OP_LBU:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef LW
		OP_LH:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef LHU
		OP_LHU:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef LUI
		OP_LUI:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 1;
			ctrl_zeroer4_en = 1;
		end
		`endif
		
		`ifdef LW
		OP_LW:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef ORI
		OP_ORI:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 1;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		
		OP_REGIMM:
		casex (ifetch_rt[0])
		    `ifdef BGEZ
			FUNC_BGEZ:
			begin
				ctrl_mux2to1_pipereg_d_sel = 0;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef BLTZ			
			FUNC_BLTZ:
			begin
				ctrl_mux2to1_pipereg_d_sel = 0;
				ctrl_zeroer_en = 1;
			end
			`endif
		endcase
		
		`ifdef SB
		OP_SB:
		begin
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer0_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef SH
		OP_SH:
		begin
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer0_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef SLTI
		OP_SLTI:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		`ifdef SLTIU
		OP_SLTIU:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
		
		
		OP_SPECIAL:
		casex (ifetch_func)
		    `ifdef ADD
			FUNC_ADD:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef ADDU
			FUNC_ADDU:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef AND			
			FUNC_AND:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef JALR
			FUNC_JALR:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 0;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef JR
			FUNC_JR:
				ctrl_zeroer_en = 1;
			`endif
			
			`ifdef MFHI	
			FUNC_MFHI:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer4_en = 1;
			end
			`endif
			
			`ifdef MFLO
			FUNC_MFLO:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer4_en = 1;
			end
			`endif
			
			`ifdef MULT
			FUNC_MULT:
			begin
				ctrl_zeroer0_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef MULTU
			FUNC_MULTU:
			begin
				ctrl_zeroer0_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef NOR
			FUNC_NOR:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef OR
			FUNC_OR:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef SLL
			FUNC_SLL:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
			end
			`endif
			
			`ifdef SLLV
			FUNC_SLLV:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef SLT
			FUNC_SLT:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef SLTU
			FUNC_SLTU:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef SRA
			FUNC_SRA:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
			end
			`endif
			
			`ifdef SRAV
			FUNC_SRAV:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef SRL
			FUNC_SRL:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
			end
			`endif
			
			`ifdef SRLV
			FUNC_SRLV:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef SUB
			FUNC_SUB:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef SUBU			
			FUNC_SUBU:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
			`ifdef XOR						
			FUNC_XOR:
			begin
				ctrl_mux3to1_zeroer4_d_sel = 1;
				ctrl_zeroer0_en = 1;
				ctrl_zeroer4_en = 1;
				ctrl_zeroer_en = 1;
			end
			`endif
			
		endcase
		
		
		`ifdef SW
		OP_SW:
		begin
			ctrl_mux2to1_pipereg_d_sel = 0;
			ctrl_zeroer0_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
				
		`ifdef XORI
		OP_XORI:
		begin
			ctrl_mux3to1_zeroer4_d_sel = 2;
			ctrl_mux2to1_pipereg_d_sel = 1;
			ctrl_zeroer4_en = 1;
			ctrl_zeroer_en = 1;
		end
		`endif
	endcase
end
		//Logic for enable signals in Pipe Stage 1
always@(ifetch_opcode or ifetch_func or ifetch_rt[0] or stall_out_stage2 or haz_zeroer_q_pipereg5_q or haz_zeroer0_q_pipereg5_q)
begin
	ctrl_reg_file_b_en = 1 &~haz_zeroer0_q_pipereg5_q&~haz_zeroer_q_pipereg5_q&~stall_out_stage2;
	ctrl_reg_file_a_en = 1 &~haz_zeroer0_q_pipereg5_q&~haz_zeroer_q_pipereg5_q&~stall_out_stage2;
	ctrl_ifetch_en = 1 &~haz_zeroer0_q_pipereg5_q&~haz_zeroer_q_pipereg5_q&~stall_out_stage2;
end
		//Decode Logic for Opcode and Multiplex Select signals
always@(pipereg8_q or pipereg9_q or pipereg10_q or addersub_result)
begin
		// Initialize control opcodes to zero
	ctrl_mux3to1_nop_d_sel = 0;
	ctrl_mux2to1_addersub_opA_sel = 0;
	ctrl_mux7to1_reg_file_c_writedatain_sel = 0;
	ctrl_mux6to1_ifetch_load_sel = 0;
	ctrl_mux3to1_ifetch_load_data_sel = 0;
	ctrl_mux3to1_shifter_sa_sel = 0;
	ctrl_addersub_op = 0;
	ctrl_ifetch_op = 0;
	ctrl_data_mem_op = 0;
	ctrl_mul_op = 0;
	ctrl_logic_unit_op = 0;
	ctrl_shifter_op = 0;
	
	casex (pipereg8_q)
	    `ifdef ADDI
		OP_ADDI:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 6;
			ctrl_addersub_op = 3;
		end
		`endif
		
		`ifdef ADDIU
		OP_ADDIU:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 6;
			ctrl_addersub_op = 1;
		end
		`endif
		
		`ifdef ANDI
		OP_ANDI:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 4;
			ctrl_logic_unit_op = 0;
		end
		`endif
		
		`ifdef BEQ
		OP_BEQ:
		begin
			ctrl_mux6to1_ifetch_load_sel = 5;
			ctrl_mux3to1_ifetch_load_data_sel = 2;
			ctrl_ifetch_op = 0;
		end
		`endif
		
		`ifdef BGTZ
		OP_BGTZ:
		begin
			ctrl_mux6to1_ifetch_load_sel = 0;
			ctrl_mux3to1_ifetch_load_data_sel = 2;
			ctrl_ifetch_op = 0;
		end
		`endif
		
		`ifdef BLEZ
		OP_BLEZ:
		begin
			ctrl_mux6to1_ifetch_load_sel = 3;
			ctrl_mux3to1_ifetch_load_data_sel = 2;
			ctrl_ifetch_op = 0;
		end
		`endif
		
		`ifdef BNE
		OP_BNE:
		begin
			ctrl_mux6to1_ifetch_load_sel = 4;
			ctrl_mux3to1_ifetch_load_data_sel = 2;
			ctrl_ifetch_op = 0;
		end
		`endif
		
		`ifdef J
		OP_J:
		begin
			ctrl_mux3to1_ifetch_load_data_sel = 1;
			ctrl_ifetch_op = 1;
		end
		`endif
		
		`ifdef JAL
		OP_JAL:
		begin
			ctrl_mux2to1_addersub_opA_sel = 1;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 6;
			ctrl_mux3to1_ifetch_load_data_sel = 1;
			ctrl_addersub_op = 1;
			ctrl_ifetch_op = 1;
		end
		`endif
		
		`ifdef LB
		OP_LB:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 2;
			ctrl_addersub_op = 3;
			ctrl_data_mem_op = 7;
		end
		`endif
		
		`ifdef LBU
		OP_LBU:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 2;
			ctrl_addersub_op = 3;
			ctrl_data_mem_op = 3;
		end
		`endif
		
		`ifdef LH
		OP_LH:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 2;
			ctrl_addersub_op = 3;
			ctrl_data_mem_op = 5;
		end
		`endif
		
		`ifdef LHU
		OP_LHU:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 2;
			ctrl_addersub_op = 3;
			ctrl_data_mem_op = 1;
		end
		`endif
		
		`ifdef LUI
		OP_LUI:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 3;
			ctrl_mux3to1_shifter_sa_sel = 1;
			ctrl_shifter_op = 0;
		end
		`endif
		
		`ifdef LW
		OP_LW:
		begin
			
			casex(addersub_result)
		       NorthIn:       begin ctrl_mux7to1_reg_file_c_writedatain_sel = 8;  end
		       SouthIn:       begin ctrl_mux7to1_reg_file_c_writedatain_sel = 9;  end
		       EastIn:        begin ctrl_mux7to1_reg_file_c_writedatain_sel = 10; end
		       WestIn:        begin ctrl_mux7to1_reg_file_c_writedatain_sel = 11; end
		       NorthEmptyPort:begin ctrl_mux7to1_reg_file_c_writedatain_sel = 12; end
		       SouthEmptyPort:begin ctrl_mux7to1_reg_file_c_writedatain_sel = 13; end
		       EastEmptyPort: begin ctrl_mux7to1_reg_file_c_writedatain_sel = 14; end
		       WestEmptyPort: begin ctrl_mux7to1_reg_file_c_writedatain_sel = 15; end
			   NorthFullPort: begin ctrl_mux7to1_reg_file_c_writedatain_sel = 16; end
			   SouthFullPort: begin ctrl_mux7to1_reg_file_c_writedatain_sel = 17; end
			   EastFullPort:  begin ctrl_mux7to1_reg_file_c_writedatain_sel = 18; end
			   WestFullPort:  begin ctrl_mux7to1_reg_file_c_writedatain_sel = 19; end
			   default:       begin ctrl_mux7to1_reg_file_c_writedatain_sel = 2; end
			endcase
			   
			 
			    
			ctrl_mux3to1_nop_d_sel = 2;			            			
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_addersub_op = 3;
			ctrl_data_mem_op = 0;
		end
		`endif
		
		`ifdef ORI
		OP_ORI:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 4;
			ctrl_logic_unit_op = 1;
		end
		`endif
		
		`ifdef REGIMM
		OP_REGIMM:
		casex (pipereg10_q[0])
		    `ifdef BGEZ
			FUNC_BGEZ:
			begin
				ctrl_mux6to1_ifetch_load_sel = 1;
				ctrl_mux3to1_ifetch_load_data_sel = 2;
				ctrl_ifetch_op = 0;
			end
			`endif
			
			`ifdef BLTZ
			FUNC_BLTZ:
			begin
				ctrl_mux6to1_ifetch_load_sel = 2;
				ctrl_mux3to1_ifetch_load_data_sel = 2;
				ctrl_ifetch_op = 0;
			end
			`endif
		endcase
		`endif
		`ifdef SB
		OP_SB:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_addersub_op = 3;
			ctrl_data_mem_op = 11;
		end
		`endif
		
		`ifdef SH
		OP_SH:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_addersub_op = 3;
			ctrl_data_mem_op = 9;
		end
		`endif
		
		`ifdef SLTI
		OP_SLTI:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 5;
			ctrl_addersub_op = 6;
		end
		`endif
		
		`ifdef SLTIU
		OP_SLTIU:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 5;
			ctrl_addersub_op = 4;
		end
		`endif
		
		
		OP_SPECIAL:
		casex (pipereg9_q)
		    `ifdef ADD
			FUNC_ADD:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux2to1_addersub_opA_sel = 0;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 6;
				ctrl_addersub_op = 3;
			end
			`endif
			
			`ifdef ADDU
			FUNC_ADDU:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux2to1_addersub_opA_sel = 0;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 6;
				ctrl_addersub_op = 1;
			end
			`endif
			
			`ifdef AND
			FUNC_AND:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 4;
				ctrl_logic_unit_op = 0;
			end
			`endif
			
			`ifdef JALR
			FUNC_JALR:
			begin
				ctrl_mux2to1_addersub_opA_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 6;
				ctrl_mux3to1_ifetch_load_data_sel = 0;
				ctrl_addersub_op = 1;
				ctrl_ifetch_op = 1;
			end
			`endif
			
			`ifdef JR
			FUNC_JR:
			begin
				ctrl_mux3to1_ifetch_load_data_sel = 0;
				ctrl_ifetch_op = 1;
			end
			`endif
			
			`ifdef MFHI			
			FUNC_MFHI:
				ctrl_mux7to1_reg_file_c_writedatain_sel = 1;
			`endif
			
			`ifdef MFLO
			FUNC_MFLO:
				ctrl_mux7to1_reg_file_c_writedatain_sel = 0;
			`endif
			
			`ifdef MULT
			FUNC_MULT:
				ctrl_mul_op = 1;
			`endif
			
			`ifdef MULTU
			FUNC_MULTU:
				ctrl_mul_op = 0;
			`endif
			
			`ifdef NOR
			FUNC_NOR:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 4;
				ctrl_logic_unit_op = 3;
			end
			`endif
			
			`ifdef OR			
			FUNC_OR:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 4;
				ctrl_logic_unit_op = 1;
			end
			`endif
			
			`ifdef SLL
			FUNC_SLL:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 3;
				ctrl_mux3to1_shifter_sa_sel = 0;
				ctrl_shifter_op = 0;
			end
			`endif
			
			`ifdef SLLV			
			FUNC_SLLV:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 3;
				ctrl_mux3to1_shifter_sa_sel = 2;
				ctrl_shifter_op = 0;
			end
			`endif
			
			`ifdef SLT						
			FUNC_SLT:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux2to1_addersub_opA_sel = 0;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 5;
				ctrl_addersub_op = 6;
			end
			`endif
			
			`ifdef SLTU
			FUNC_SLTU:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux2to1_addersub_opA_sel = 0;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 5;
				ctrl_addersub_op = 4;
			end
			`endif
			
			`ifdef SRA
			FUNC_SRA:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 3;
				ctrl_mux3to1_shifter_sa_sel = 0;
				ctrl_shifter_op = 3;
			end
			`endif
			
			`ifdef SRAV
			FUNC_SRAV:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 3;
				ctrl_mux3to1_shifter_sa_sel = 2;
				ctrl_shifter_op = 3;
			end
			`endif
			
			`ifdef SRL
			FUNC_SRL:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 3;
				ctrl_mux3to1_shifter_sa_sel = 0;
				ctrl_shifter_op = 1;
			end
			`endif
			
			`ifdef SRLV
			FUNC_SRLV:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 3;
				ctrl_mux3to1_shifter_sa_sel = 2;
				ctrl_shifter_op = 1;
			end
			`endif
			
			`ifdef SUB
			FUNC_SUB:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux2to1_addersub_opA_sel = 0;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 6;
				ctrl_addersub_op = 0;
			end
			`endif
			
			`ifdef SUBU
			FUNC_SUBU:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux2to1_addersub_opA_sel = 0;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 6;
				ctrl_addersub_op = 2;
			end
			`endif
			
			`ifdef XOR
			FUNC_XOR:
			begin
				ctrl_mux3to1_nop_d_sel = 1;
				ctrl_mux7to1_reg_file_c_writedatain_sel = 4;
				ctrl_logic_unit_op = 2;
			end
			`endif
		endcase
	    `ifdef SW
		OP_SW:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux2to1_addersub_opA_sel = 0;
			ctrl_addersub_op = 3;
			ctrl_data_mem_op = 8;
		end
		`endif
		
		`ifdef XORI
		OP_XORI:
		begin
			ctrl_mux3to1_nop_d_sel = 2;
			ctrl_mux7to1_reg_file_c_writedatain_sel = 4;
			ctrl_logic_unit_op = 2;
		end
		`endif
	endcase
end
		//Logic for enable signals in Pipe Stage 2
always@(pipereg8_q or pipereg9_q or pipereg10_q[0] or 1'b0 or ctrl_shifter_stalled or ctrl_data_mem_stalled)
begin
	ctrl_reg_file_c_we = 0;
	ctrl_lo_reg_en = 0;
	ctrl_branchresolve_en = 0;
	ctrl_hi_reg_en = 0;
	ctrl_ifetch_we = 0;
	ctrl_data_mem_en = 0;
	ctrl_shifter_start = 0;
	casex (pipereg8_q)
		
		`ifdef ADDI
		OP_ADDI:
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		`endif
		
		`ifdef ADDIU			
		OP_ADDIU:
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		`endif
		
		`ifdef ANDI		
		OP_ANDI:
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		`endif
		
		`ifdef BEQ
		OP_BEQ:
		begin
			ctrl_branchresolve_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		end
		`endif
		
		`ifdef BGTZ
		OP_BGTZ:
		begin
			ctrl_branchresolve_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		end
		`endif
		
		`ifdef BLEZ
		OP_BLEZ:
		begin
			ctrl_branchresolve_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		end
		`endif
		
		`ifdef BNE
		OP_BNE:
		begin
			ctrl_branchresolve_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		end
		`endif
		
		`ifdef J
		OP_J:
			ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		`endif
		
		`ifdef JAL			
		OP_JAL:
		begin
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		end
		`endif
		
		`ifdef LB
		OP_LB:
		begin
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_data_mem_en = 1 &~1'b0;
		end
		`endif
		
		`ifdef LBU
		OP_LBU:
		begin
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_data_mem_en = 1 &~1'b0;
		end
		`endif
		
		`ifdef LH
		OP_LH:
		begin
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_data_mem_en = 1 &~1'b0;
		end
		`endif
		
		`ifdef LHU
		OP_LHU:
		begin
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_data_mem_en = 1 &~1'b0;
		end
		`endif
		
		`ifdef LUI
		OP_LUI:
		begin
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_shifter_start = 1 &~1'b0;
		end
		`endif
		
		`ifdef LW
		OP_LW:
		begin
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			ctrl_data_mem_en = 1 &~1'b0;
		end
		`endif
		
		`ifdef ORI		
		OP_ORI:
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		`endif
		
		OP_REGIMM:
		casex (pipereg10_q[0])
		   `ifdef BGEZ			
			FUNC_BGEZ:
			begin
				ctrl_branchresolve_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			end
			`endif
			
			`ifdef BLTZ			
			FUNC_BLTZ:
			begin
				ctrl_branchresolve_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			end
		    `endif
		endcase
		
		`ifdef SB
		OP_SB:
			ctrl_data_mem_en = 1 &~1'b0;
		`endif
		
		`ifdef SH	
		OP_SH:
			ctrl_data_mem_en = 1 &~1'b0;
		`endif
		
		`ifdef SLTI				
		OP_SLTI:
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		`endif
		
		`ifdef SLTIU
		OP_SLTIU:
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		`endif
		

		OP_SPECIAL:
		casex (pipereg9_q)
		    `ifdef ADD
			FUNC_ADD:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		    `endif
		    
		    `ifdef ADDU			  
			FUNC_ADDU:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		    `endif
		    
		    `ifdef AND
			FUNC_AND:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		    `endif
		    
		    `ifdef JALR
			FUNC_JALR:
			begin
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			end
		    `endif
		    
		    `ifdef JR
			FUNC_JR:
				ctrl_ifetch_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef MFHI
			FUNC_MFHI:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef MFLO
			FUNC_MFLO:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef MULT
			FUNC_MULT:
			begin
				ctrl_lo_reg_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_hi_reg_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			end
			`endif
			
			`ifdef MULTU
			FUNC_MULTU:
			begin
				ctrl_lo_reg_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_hi_reg_en = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			end
			`endif
			
			`ifdef NOR
			FUNC_NOR:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef OR
			FUNC_OR:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef SLL
			FUNC_SLL:
			begin
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_shifter_start = 1 &~1'b0;
			end
			`endif
			
			`ifdef SLLV
			FUNC_SLLV:
			begin
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_shifter_start = 1 &~1'b0;
			end
			`endif
			
			`ifdef SLT
			FUNC_SLT:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef SLTU
			FUNC_SLTU:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef SRA
			FUNC_SRA:
			begin
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_shifter_start = 1 &~1'b0;
			end
			`endif
			
			`ifdef SRAV
			FUNC_SRAV:
			begin
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_shifter_start = 1 &~1'b0;
			end
			`endif
			
			`ifdef SRL
			FUNC_SRL:
			begin
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_shifter_start = 1 &~1'b0;
			end
			`endif
			
			`ifdef SRLV
			FUNC_SRLV:
			begin
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
				ctrl_shifter_start = 1 &~1'b0;
			end
			`endif
			
			`ifdef SUB
			FUNC_SUB:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef SUB
			FUNC_SUBU:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif
			
			`ifdef XOR
			FUNC_XOR:
				ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
			`endif	
		endcase
		
		`ifdef SW
		OP_SW:
			ctrl_data_mem_en = 1 &~1'b0;
		`endif
		
		`ifdef XORI			
		OP_XORI:
			ctrl_reg_file_c_we = 1 &~ctrl_data_mem_stalled&~ctrl_shifter_stalled&~1'b0;
		`endif	
	endcase
end

/********* Stall Network & PipeReg Control ********/
assign stall_out_stage1 = stall_out_stage2|haz_zeroer0_q_pipereg5_q|haz_zeroer_q_pipereg5_q;
assign ctrl_pipereg10_en = ~stall_out_stage1;
assign ctrl_pipereg9_en = ~stall_out_stage1;
assign ctrl_pipereg8_en = ~stall_out_stage1;
assign ctrl_pipereg1_en = ~stall_out_stage1;
assign ctrl_pipereg3_en = ~stall_out_stage1;
assign ctrl_pipereg2_en = ~stall_out_stage1;
assign ctrl_pipereg5_en = ~stall_out_stage1;
assign ctrl_pipereg_en = ~stall_out_stage1;
assign stall_out_stage2 = 1'b0|ctrl_data_mem_stalled|ctrl_shifter_stalled;
assign branch_mispred = (((ctrl_ifetch_op==1) || (ctrl_ifetch_op==0 && mux6to1_ifetch_load_out)) & ctrl_ifetch_we);
assign stall_2nd_delayslot = &has_delayslot;
assign has_delayslot = 0;
assign squash_stage1 = ((stall_out_stage1&~stall_out_stage2))|~resetn;
assign ctrl_pipereg10_resetn = ~squash_stage1;
assign ctrl_pipereg9_resetn = ~squash_stage1;
assign ctrl_pipereg8_resetn = ~squash_stage1;
assign ctrl_pipereg1_resetn = ~squash_stage1;
assign ctrl_pipereg3_resetn = ~squash_stage1;
assign ctrl_pipereg2_resetn = ~squash_stage1;
assign ctrl_pipereg5_resetn = ~squash_stage1;
assign ctrl_pipereg_resetn = ~squash_stage1;
assign ctrl_pipereg_squashn = ~(0);
assign ctrl_pipereg5_squashn = ~(0);
assign ctrl_pipereg2_squashn = ~(0);
assign ctrl_pipereg3_squashn = ~(0);
assign ctrl_pipereg1_squashn = ~(0);
assign ctrl_pipereg8_squashn = ~(0);
assign ctrl_pipereg9_squashn = ~(0);
assign ctrl_pipereg10_squashn = ~(0);
assign ctrl_ifetch_squashn = ~(0);
assign squash_stage2 = ((stall_out_stage2&~1'b0))|~resetn;

/****************************** Datapath **************************/
/******************** Hazard Detection Logic ***********************/
assign haz_zeroer0_q_pipereg5_q = (zeroer0_q==pipereg5_q) && (|zeroer0_q);
assign haz_zeroer_q_pipereg5_q = (zeroer_q==pipereg5_q) && (|zeroer_q);

/*************** DATAPATH COMPONENTS **************/
addersub addersub (
	.opB(nop_q),
	.opA(mux2to1_addersub_opA_out),
	.op(ctrl_addersub_op),
	.result_slt(addersub_result_slt),
	.result(addersub_result));

logic_unit logic_unit (
	.opB(nop_q),
	.opA(reg_file_a_readdataout),
	.op(ctrl_logic_unit_op),
	.result(logic_unit_result));
	defparam
		logic_unit.WIDTH=32;

shifter shifter (
	.clk(clk),
	.resetn(resetn),
	.dst(pipereg5_q),
	.sa(mux3to1_shifter_sa_out),
	.opB(nop_q),
	.op(ctrl_shifter_op),
	.start(ctrl_shifter_start),
	.stalled(ctrl_shifter_stalled),
	.result(shifter_result));
	defparam
		shifter.WIDTH=32;

mul mul (
	.opB(reg_file_b_readdataout),
	.opA(reg_file_a_readdataout),
	.op(ctrl_mul_op),
	.lo(mul_lo),
	.hi(mul_hi));

ifetch ifetch (
	.clk(clk),
	.resetn(resetn),
	.boot_iaddr(boot_iaddr),
	.boot_idata(boot_idata),
	.boot_iwe(boot_iwe),
	.load(mux6to1_ifetch_load_out),
	.load_data(mux3to1_ifetch_load_data_out),
	.op(ctrl_ifetch_op),
	.we(ctrl_ifetch_we),
	.squashn(ctrl_ifetch_squashn),
	.en(ctrl_ifetch_en),
	.pc_out(ifetch_pc_out),
	.instr(ifetch_instr),
	.opcode(ifetch_opcode),
	.func(ifetch_func),
	.rs(ifetch_rs),
	.rt(ifetch_rt),
	.rd(ifetch_rd),
	.instr_index(ifetch_instr_index),
	.offset(ifetch_offset),
	.sa(ifetch_sa),
	.next_pc(ifetch_next_pc));

data_mem data_mem (
	.clk(clk),
	.resetn(resetn),
	.boot_daddr(boot_daddr),
	.boot_ddata(boot_ddata),
	.boot_dwe(boot_dwe),
	.d_address(addersub_result),
	.d_writedata(reg_file_b_readdataout),
	.op(ctrl_data_mem_op),
	.en(ctrl_data_mem_en),
	.stalled(ctrl_data_mem_stalled),
	.d_loadresult(data_mem_d_loadresult));

pcadder pcadder (
	.offset(pipereg_q),
	.pc(pipereg3_q),
	.result(pcadder_result));

signext16 signext16 (
	.in(ifetch_offset),
	.out(signext16_out));

reg_file reg_file (
	.clk(clk),
	.resetn(resetn),
	.c_writedatain(mux7to1_reg_file_c_writedatain_out),
	.c_reg(pipereg5_q),
	.b_reg(zeroer0_q),
	.a_reg(zeroer_q),
	.c_we(ctrl_reg_file_c_we),
	.b_en(ctrl_reg_file_b_en),
	.a_en(ctrl_reg_file_a_en),
	.b_readdataout(reg_file_b_readdataout),
	.a_readdataout(reg_file_a_readdataout));

merge26lo merge26lo (
	.in2(pipereg1_q),
	.in1(pipereg3_q),
	.out(merge26lo_out));

branchresolve branchresolve (
	.rt(reg_file_b_readdataout),
	.rs(reg_file_a_readdataout),
	.en(ctrl_branchresolve_en),
	.eqz(branchresolve_eqz),
	.gez(branchresolve_gez),
	.gtz(branchresolve_gtz),
	.lez(branchresolve_lez),
	.ltz(branchresolve_ltz),
	.ne(branchresolve_ne),
	.eq(branchresolve_eq));
	defparam
		branchresolve.WIDTH=32;

hi_reg hi_reg (
	.clk(clk),
	.resetn(resetn),
	.d(mul_hi),
	.en(ctrl_hi_reg_en),
	.q(hi_reg_q));
	defparam
		hi_reg.WIDTH=32;

lo_reg lo_reg (
	.clk(clk),
	.resetn(resetn),
	.d(mul_lo),
	.en(ctrl_lo_reg_en),
	.q(lo_reg_q));
	defparam
		lo_reg.WIDTH=32;

constant const6 (
	.out(const6_out));
	defparam
		const6.WIDTH=32,
		const6.VAL=0;

constant const7 (
	.out(const7_out));
	defparam
		const7.WIDTH=32,
		const7.VAL=16;

constant constant (
	.out(const_out));
	defparam
		constant.WIDTH=32,
		constant.VAL=31;

pipereg pipereg (
	.clk(clk),
	.resetn(ctrl_pipereg_resetn),
	.d(mux2to1_pipereg_d_out),
	.squashn(ctrl_pipereg_squashn),
	.en(ctrl_pipereg_en),
	.q(pipereg_q));
	defparam
		pipereg.WIDTH=32;

pipereg pipereg1 (
	.clk(clk),
	.resetn(ctrl_pipereg1_resetn),
	.d(ifetch_instr_index),
	.squashn(ctrl_pipereg1_squashn),
	.en(ctrl_pipereg1_en),
	.q(pipereg1_q));
	defparam
		pipereg1.WIDTH=26;

pipereg pipereg2 (
	.clk(clk),
	.resetn(ctrl_pipereg2_resetn),
	.d(ifetch_sa),
	.squashn(ctrl_pipereg2_squashn),
	.en(ctrl_pipereg2_en),
	.q(pipereg2_q));
	defparam
		pipereg2.WIDTH=5;

pipereg pipereg5 (
	.clk(clk),
	.resetn(ctrl_pipereg5_resetn),
	.d(zeroer4_q),
	.squashn(ctrl_pipereg5_squashn),
	.en(ctrl_pipereg5_en),
	.q(pipereg5_q));
	defparam
		pipereg5.WIDTH=5;

pipereg pipereg3 (
	.clk(clk),
	.resetn(ctrl_pipereg3_resetn),
	.d(ifetch_pc_out),
	.squashn(ctrl_pipereg3_squashn),
	.en(ctrl_pipereg3_en),
	.q(pipereg3_q));
	defparam
		pipereg3.WIDTH=32;

fakedelay fakedelay (
	.clk(clk),
	.d(ifetch_pc_out),
	.q(fakedelay_q));
	defparam
		fakedelay.WIDTH=32;

nop nop (
	.d(mux3to1_nop_d_out),
	.q(nop_q));
	defparam
		nop.WIDTH=32;

zeroer zeroer (
	.d(ifetch_rs),
	.en(ctrl_zeroer_en),
	.q(zeroer_q));
	defparam
		zeroer.WIDTH=5;

zeroer zeroer0 (
	.d(ifetch_rt),
	.en(ctrl_zeroer0_en),
	.q(zeroer0_q));
	defparam
		zeroer0.WIDTH=5;

zeroer zeroer4 (
	.d(mux3to1_zeroer4_d_out),
	.en(ctrl_zeroer4_en),
	.q(zeroer4_q));
	defparam
		zeroer4.WIDTH=5;

		// Multiplexor mux3to1_shifter_sa instantiation
assign mux3to1_shifter_sa_out = 
	(ctrl_mux3to1_shifter_sa_sel==2) ? reg_file_a_readdataout :
	(ctrl_mux3to1_shifter_sa_sel==1) ? const7_out :
	pipereg2_q;

		// Multiplexor mux3to1_ifetch_load_data instantiation
assign mux3to1_ifetch_load_data_out = 
	(ctrl_mux3to1_ifetch_load_data_sel==2) ? pcadder_result :
	(ctrl_mux3to1_ifetch_load_data_sel==1) ? merge26lo_out :
	reg_file_a_readdataout;

		// Multiplexor mux6to1_ifetch_load instantiation
assign mux6to1_ifetch_load_out = 
	(ctrl_mux6to1_ifetch_load_sel==5) ? branchresolve_eq :
	(ctrl_mux6to1_ifetch_load_sel==4) ? branchresolve_ne :
	(ctrl_mux6to1_ifetch_load_sel==3) ? branchresolve_lez :
	(ctrl_mux6to1_ifetch_load_sel==2) ? branchresolve_ltz :
	(ctrl_mux6to1_ifetch_load_sel==1) ? branchresolve_gez :
	branchresolve_gtz;

		// Multiplexor mux7to1_reg_file_c_writedatain instantiation
assign mux7to1_reg_file_c_writedatain_out = 
	(ctrl_mux7to1_reg_file_c_writedatain_sel==6) ? addersub_result :
	(ctrl_mux7to1_reg_file_c_writedatain_sel==5) ? addersub_result_slt :
	(ctrl_mux7to1_reg_file_c_writedatain_sel==4) ? logic_unit_result :
	(ctrl_mux7to1_reg_file_c_writedatain_sel==3) ? shifter_result :
	(ctrl_mux7to1_reg_file_c_writedatain_sel==2) ? data_mem_d_loadresult :
	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==8) ? tempFifoDataInNorth : //Deepak
	(ctrl_mux7to1_reg_file_c_writedatain_sel==9) ? tempFifoDataInSouth : //Deepak
	(ctrl_mux7to1_reg_file_c_writedatain_sel==10)? tempFifoDataInEast : //Deepak
	(ctrl_mux7to1_reg_file_c_writedatain_sel==11)? tempFifoDataInWest : //Deepak	

	(ctrl_mux7to1_reg_file_c_writedatain_sel==12)? northEmpty : //Deepak	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==13)? southEmpty : //Deepak	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==14)? eastEmpty  : //Deepak	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==15)? westEmpty  : //Deepak	
	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==16)? northFull  : //Deepak	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==17)? southFull  : //Deepak	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==18)? eastFull   : //Deepak	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==19)? westFull   : //Deepak	
	
	(ctrl_mux7to1_reg_file_c_writedatain_sel==1) ? hi_reg_q :
	lo_reg_q;

		// Multiplexor mux2to1_addersub_opA instantiation
assign mux2to1_addersub_opA_out = 
	(ctrl_mux2to1_addersub_opA_sel==1) ? fakedelay_q :
	reg_file_a_readdataout;

		// Multiplexor mux2to1_pipereg_d instantiation
assign mux2to1_pipereg_d_out = 
	(ctrl_mux2to1_pipereg_d_sel==1) ? ifetch_offset :
	signext16_out;

		// Multiplexor mux3to1_zeroer4_d instantiation
assign mux3to1_zeroer4_d_out = 
	(ctrl_mux3to1_zeroer4_d_sel==2) ? ifetch_rt :
	(ctrl_mux3to1_zeroer4_d_sel==1) ? ifetch_rd :
	const_out;

		// Multiplexor mux3to1_nop_d instantiation
assign mux3to1_nop_d_out = 
	(ctrl_mux3to1_nop_d_sel==2) ? pipereg_q :
	(ctrl_mux3to1_nop_d_sel==1) ? reg_file_b_readdataout :
	const6_out;

pipereg pipereg8 (
	.clk(clk),
	.resetn(ctrl_pipereg8_resetn),
	.d(ifetch_opcode),
	.squashn(ctrl_pipereg8_squashn),
	.en(ctrl_pipereg8_en),
	.q(pipereg8_q));
	defparam
		pipereg8.WIDTH=6;

pipereg pipereg9 (
	.clk(clk),
	.resetn(ctrl_pipereg9_resetn),
	.d(ifetch_func),
	.squashn(ctrl_pipereg9_squashn),
	.en(ctrl_pipereg9_en),
	.q(pipereg9_q));
	defparam
		pipereg9.WIDTH=6;

pipereg pipereg10 (
	.clk(clk),
	.resetn(ctrl_pipereg10_resetn),
	.d(ifetch_rt),
	.squashn(ctrl_pipereg10_squashn),
	.en(ctrl_pipereg10_en),
	.q(pipereg10_q));
	defparam
		pipereg10.WIDTH=5;



endmodule


`timescale 1ns / 1ns
module system50(clk,resetn,boot_iaddr,boot_idata,boot_daddr,boot_ddata,reg_file_b_readdataout,processor_select);
    input clk;
    input resetn;
    input [6:0] processor_select;
    output [31:0] reg_file_b_readdataout;
    input [13:0] boot_iaddr;
    input [31:0] boot_idata;
    input [13:0] boot_daddr;
    input [31:0] boot_ddata;


    reg boot_iwe0;
    reg boot_dwe0;
    reg boot_iwe1;
    reg boot_dwe1;
    reg boot_iwe2;
    reg boot_dwe2;
    reg boot_iwe3;
    reg boot_dwe3;
    reg boot_iwe4;
    reg boot_dwe4;
    reg boot_iwe5;
    reg boot_dwe5;
    reg boot_iwe6;
    reg boot_dwe6;
    reg boot_iwe7;
    reg boot_dwe7;
    reg boot_iwe8;
    reg boot_dwe8;
    reg boot_iwe9;
    reg boot_dwe9;
    reg boot_iwe10;
    reg boot_dwe10;
    reg boot_iwe11;
    reg boot_dwe11;
    reg boot_iwe12;
    reg boot_dwe12;
    reg boot_iwe13;
    reg boot_dwe13;
    reg boot_iwe14;
    reg boot_dwe14;
    reg boot_iwe15;
    reg boot_dwe15;
    reg boot_iwe16;
    reg boot_dwe16;
    reg boot_iwe17;
    reg boot_dwe17;
    reg boot_iwe18;
    reg boot_dwe18;
    reg boot_iwe19;
    reg boot_dwe19;
    reg boot_iwe20;
    reg boot_dwe20;
    reg boot_iwe21;
    reg boot_dwe21;
    reg boot_iwe22;
    reg boot_dwe22;
    reg boot_iwe23;
    reg boot_dwe23;
    reg boot_iwe24;
    reg boot_dwe24;
    reg boot_iwe25;
    reg boot_dwe25;
    reg boot_iwe26;
    reg boot_dwe26;
    reg boot_iwe27;
    reg boot_dwe27;
    reg boot_iwe28;
    reg boot_dwe28;
    reg boot_iwe29;
    reg boot_dwe29;
    reg boot_iwe30;
    reg boot_dwe30;
    reg boot_iwe31;
    reg boot_dwe31;
    reg boot_iwe32;
    reg boot_dwe32;
    reg boot_iwe33;
    reg boot_dwe33;
    reg boot_iwe34;
    reg boot_dwe34;
    reg boot_iwe35;
    reg boot_dwe35;
    reg boot_iwe36;
    reg boot_dwe36;
    reg boot_iwe37;
    reg boot_dwe37;
    reg boot_iwe38;
    reg boot_dwe38;
    reg boot_iwe39;
    reg boot_dwe39;
    reg boot_iwe40;
    reg boot_dwe40;
    reg boot_iwe41;
    reg boot_dwe41;
    reg boot_iwe42;
    reg boot_dwe42;
    reg boot_iwe43;
    reg boot_dwe43;
    reg boot_iwe44;
    reg boot_dwe44;
    reg boot_iwe45;
    reg boot_dwe45;
    reg boot_iwe46;
    reg boot_dwe46;
    reg boot_iwe47;
    reg boot_dwe47;
    reg boot_iwe48;
    reg boot_dwe48;
    reg boot_iwe49;
    reg boot_dwe49;

     //Processor 0 control and data signals
    wire wrProc0South;
    wire fullProc0South;
    wire [31:0] dataOutProc0South;

     //Processor 0 control and data signals
    wire rdProc0East;
    wire emptyProc0East;
    wire [31:0] dataInProc0East;

     //Processor 0 control and data signals
    wire wrProc0East;
    wire fullProc0East;
    wire [31:0] dataOutProc0East;

     //Processor 1 control and data signals
    wire rdProc1West;
    wire emptyProc1West;
    wire [31:0] dataInProc1West;

     //Processor 1 control and data signals
    wire wrProc1West;
    wire fullProc1West;
    wire [31:0] dataOutProc1West;

     //Processor 2 control and data signals
    wire rdProc2East;
    wire emptyProc2East;
    wire [31:0] dataInProc2East;

     //Processor 3 control and data signals
    wire rdProc3East;
    wire emptyProc3East;
    wire [31:0] dataInProc3East;

     //Processor 3 control and data signals
    wire wrProc3West;
    wire fullProc3West;
    wire [31:0] dataOutProc3West;

     //Processor 4 control and data signals
    wire rdProc4East;
    wire emptyProc4East;
    wire [31:0] dataInProc4East;

     //Processor 4 control and data signals
    wire wrProc4West;
    wire fullProc4West;
    wire [31:0] dataOutProc4West;

     //Processor 5 control and data signals
    wire rdProc5East;
    wire emptyProc5East;
    wire [31:0] dataInProc5East;

     //Processor 5 control and data signals
    wire wrProc5West;
    wire fullProc5West;
    wire [31:0] dataOutProc5West;

     //Processor 6 control and data signals
    wire rdProc6South;
    wire emptyProc6South;
    wire [31:0] dataInProc6South;

     //Processor 6 control and data signals
    wire wrProc6South;
    wire fullProc6South;
    wire [31:0] dataOutProc6South;

     //Processor 6 control and data signals
    wire rdProc6East;
    wire emptyProc6East;
    wire [31:0] dataInProc6East;

     //Processor 6 control and data signals
    wire wrProc6West;
    wire fullProc6West;
    wire [31:0] dataOutProc6West;

     //Processor 7 control and data signals
    wire wrProc7South;
    wire fullProc7South;
    wire [31:0] dataOutProc7South;

     //Processor 7 control and data signals
    wire rdProc7East;
    wire emptyProc7East;
    wire [31:0] dataInProc7East;

     //Processor 7 control and data signals
    wire wrProc7West;
    wire fullProc7West;
    wire [31:0] dataOutProc7West;

     //Processor 8 control and data signals
    wire rdProc8South;
    wire emptyProc8South;
    wire [31:0] dataInProc8South;

     //Processor 8 control and data signals
    wire rdProc8East;
    wire emptyProc8East;
    wire [31:0] dataInProc8East;

     //Processor 8 control and data signals
    wire wrProc8West;
    wire fullProc8West;
    wire [31:0] dataOutProc8West;

     //Processor 9 control and data signals
    wire rdProc9South;
    wire emptyProc9South;
    wire [31:0] dataInProc9South;

     //Processor 9 control and data signals
    wire wrProc9West;
    wire fullProc9West;
    wire [31:0] dataOutProc9West;

     //Processor 10 control and data signals
    wire rdProc10North;
    wire emptyProc10North;
    wire [31:0] dataInProc10North;

     //Processor 10 control and data signals
    wire wrProc10South;
    wire fullProc10South;
    wire [31:0] dataOutProc10South;

     //Processor 11 control and data signals
    wire rdProc11South;
    wire emptyProc11South;
    wire [31:0] dataInProc11South;

     //Processor 11 control and data signals
    wire wrProc11East;
    wire fullProc11East;
    wire [31:0] dataOutProc11East;

     //Processor 12 control and data signals
    wire rdProc12South;
    wire emptyProc12South;
    wire [31:0] dataInProc12South;

     //Processor 12 control and data signals
    wire wrProc12South;
    wire fullProc12South;
    wire [31:0] dataOutProc12South;

     //Processor 12 control and data signals
    wire wrProc12East;
    wire fullProc12East;
    wire [31:0] dataOutProc12East;

     //Processor 12 control and data signals
    wire rdProc12West;
    wire emptyProc12West;
    wire [31:0] dataInProc12West;

     //Processor 13 control and data signals
    wire wrProc13East;
    wire fullProc13East;
    wire [31:0] dataOutProc13East;

     //Processor 13 control and data signals
    wire rdProc13West;
    wire emptyProc13West;
    wire [31:0] dataInProc13West;

     //Processor 14 control and data signals
    wire rdProc14South;
    wire emptyProc14South;
    wire [31:0] dataInProc14South;

     //Processor 14 control and data signals
    wire wrProc14South;
    wire fullProc14South;
    wire [31:0] dataOutProc14South;

     //Processor 14 control and data signals
    wire rdProc14East;
    wire emptyProc14East;
    wire [31:0] dataInProc14East;

     //Processor 14 control and data signals
    wire wrProc14East;
    wire fullProc14East;
    wire [31:0] dataOutProc14East;

     //Processor 14 control and data signals
    wire rdProc14West;
    wire emptyProc14West;
    wire [31:0] dataInProc14West;

     //Processor 15 control and data signals
    wire wrProc15South;
    wire fullProc15South;
    wire [31:0] dataOutProc15South;

     //Processor 15 control and data signals
    wire rdProc15East;
    wire emptyProc15East;
    wire [31:0] dataInProc15East;

     //Processor 15 control and data signals
    wire wrProc15East;
    wire fullProc15East;
    wire [31:0] dataOutProc15East;

     //Processor 15 control and data signals
    wire rdProc15West;
    wire emptyProc15West;
    wire [31:0] dataInProc15West;

     //Processor 15 control and data signals
    wire wrProc15West;
    wire fullProc15West;
    wire [31:0] dataOutProc15West;

     //Processor 16 control and data signals
    wire rdProc16North;
    wire emptyProc16North;
    wire [31:0] dataInProc16North;

     //Processor 16 control and data signals
    wire wrProc16North;
    wire fullProc16North;
    wire [31:0] dataOutProc16North;

     //Processor 16 control and data signals
    wire rdProc16South;
    wire emptyProc16South;
    wire [31:0] dataInProc16South;

     //Processor 16 control and data signals
    wire wrProc16South;
    wire fullProc16South;
    wire [31:0] dataOutProc16South;

     //Processor 16 control and data signals
    wire rdProc16East;
    wire emptyProc16East;
    wire [31:0] dataInProc16East;

     //Processor 16 control and data signals
    wire rdProc16West;
    wire emptyProc16West;
    wire [31:0] dataInProc16West;

     //Processor 16 control and data signals
    wire wrProc16West;
    wire fullProc16West;
    wire [31:0] dataOutProc16West;

     //Processor 17 control and data signals
    wire rdProc17North;
    wire emptyProc17North;
    wire [31:0] dataInProc17North;

     //Processor 17 control and data signals
    wire wrProc17West;
    wire fullProc17West;
    wire [31:0] dataOutProc17West;

     //Processor 18 control and data signals
    wire wrProc18North;
    wire fullProc18North;
    wire [31:0] dataOutProc18North;

     //Processor 18 control and data signals
    wire rdProc18South;
    wire emptyProc18South;
    wire [31:0] dataInProc18South;

     //Processor 18 control and data signals
    wire rdProc18East;
    wire emptyProc18East;
    wire [31:0] dataInProc18East;

     //Processor 18 control and data signals
    wire wrProc18East;
    wire fullProc18East;
    wire [31:0] dataOutProc18East;

     //Processor 19 control and data signals
    wire wrProc19North;
    wire fullProc19North;
    wire [31:0] dataOutProc19North;

     //Processor 19 control and data signals
    wire rdProc19South;
    wire emptyProc19South;
    wire [31:0] dataInProc19South;

     //Processor 19 control and data signals
    wire rdProc19West;
    wire emptyProc19West;
    wire [31:0] dataInProc19West;

     //Processor 19 control and data signals
    wire wrProc19West;
    wire fullProc19West;
    wire [31:0] dataOutProc19West;

     //Processor 20 control and data signals
    wire rdProc20North;
    wire emptyProc20North;
    wire [31:0] dataInProc20North;

     //Processor 20 control and data signals
    wire wrProc20South;
    wire fullProc20South;
    wire [31:0] dataOutProc20South;

     //Processor 21 control and data signals
    wire wrProc21North;
    wire fullProc21North;
    wire [31:0] dataOutProc21North;

     //Processor 21 control and data signals
    wire rdProc21South;
    wire emptyProc21South;
    wire [31:0] dataInProc21South;

     //Processor 21 control and data signals
    wire wrProc21East;
    wire fullProc21East;
    wire [31:0] dataOutProc21East;

     //Processor 22 control and data signals
    wire rdProc22North;
    wire emptyProc22North;
    wire [31:0] dataInProc22North;

     //Processor 22 control and data signals
    wire wrProc22North;
    wire fullProc22North;
    wire [31:0] dataOutProc22North;

     //Processor 22 control and data signals
    wire rdProc22South;
    wire emptyProc22South;
    wire [31:0] dataInProc22South;

     //Processor 22 control and data signals
    wire wrProc22East;
    wire fullProc22East;
    wire [31:0] dataOutProc22East;

     //Processor 22 control and data signals
    wire rdProc22West;
    wire emptyProc22West;
    wire [31:0] dataInProc22West;

     //Processor 23 control and data signals
    wire rdProc23South;
    wire emptyProc23South;
    wire [31:0] dataInProc23South;

     //Processor 23 control and data signals
    wire wrProc23East;
    wire fullProc23East;
    wire [31:0] dataOutProc23East;

     //Processor 23 control and data signals
    wire rdProc23West;
    wire emptyProc23West;
    wire [31:0] dataInProc23West;

     //Processor 24 control and data signals
    wire rdProc24North;
    wire emptyProc24North;
    wire [31:0] dataInProc24North;

     //Processor 24 control and data signals
    wire wrProc24North;
    wire fullProc24North;
    wire [31:0] dataOutProc24North;

     //Processor 24 control and data signals
    wire wrProc24South;
    wire fullProc24South;
    wire [31:0] dataOutProc24South;

     //Processor 24 control and data signals
    wire wrProc24East;
    wire fullProc24East;
    wire [31:0] dataOutProc24East;

     //Processor 24 control and data signals
    wire rdProc24West;
    wire emptyProc24West;
    wire [31:0] dataInProc24West;

     //Processor 25 control and data signals
    wire rdProc25North;
    wire emptyProc25North;
    wire [31:0] dataInProc25North;

     //Processor 25 control and data signals
    wire wrProc25South;
    wire fullProc25South;
    wire [31:0] dataOutProc25South;

     //Processor 25 control and data signals
    wire wrProc25East;
    wire fullProc25East;
    wire [31:0] dataOutProc25East;

     //Processor 25 control and data signals
    wire rdProc25West;
    wire emptyProc25West;
    wire [31:0] dataInProc25West;

     //Processor 26 control and data signals
    wire rdProc26North;
    wire emptyProc26North;
    wire [31:0] dataInProc26North;

     //Processor 26 control and data signals
    wire wrProc26North;
    wire fullProc26North;
    wire [31:0] dataOutProc26North;

     //Processor 26 control and data signals
    wire rdProc26South;
    wire emptyProc26South;
    wire [31:0] dataInProc26South;

     //Processor 26 control and data signals
    wire wrProc26South;
    wire fullProc26South;
    wire [31:0] dataOutProc26South;

     //Processor 26 control and data signals
    wire rdProc26East;
    wire emptyProc26East;
    wire [31:0] dataInProc26East;

     //Processor 26 control and data signals
    wire wrProc26East;
    wire fullProc26East;
    wire [31:0] dataOutProc26East;

     //Processor 26 control and data signals
    wire rdProc26West;
    wire emptyProc26West;
    wire [31:0] dataInProc26West;

     //Processor 27 control and data signals
    wire rdProc27South;
    wire Proc27South;
    wire [31:0] dataInProc27South;

     //Processor 27 control and data signals
    wire wrProc27East;
    wire fullProc27East;
    wire [31:0] dataOutProc27East;

     //Processor 27 control and data signals
    wire rdProc27West;
    wire emptyProc27West;
    wire [31:0] dataInProc27West;

     //Processor 27 control and data signals
    wire wrProc27West;
    wire fullProc27West;
    wire [31:0] dataOutProc27West;

     //Processor 28 control and data signals
    wire wrProc28North;
    wire fullProc28North;
    wire [31:0] dataOutProc28North;

     //Processor 28 control and data signals
    wire wrProc28East;
    wire fullProc28East;
    wire [31:0] dataOutProc28East;

     //Processor 28 control and data signals
    wire rdProc28West;
    wire emptyProc28West;
    wire [31:0] dataInProc28West;

     //Processor 29 control and data signals
    wire wrProc29North;
    wire fullProc29North;
    wire [31:0] dataOutProc29North;

     //Processor 29 control and data signals
    wire rdProc29West;
    wire emptyProc29West;
    wire [31:0] dataInProc29West;

     //Processor 30 control and data signals
    wire rdProc30North;
    wire emptyProc30North;
    wire [31:0] dataInProc30North;

     //Processor 30 control and data signals
    wire wrProc30South;
    wire fullProc30South;
    wire [31:0] dataOutProc30South;

     //Processor 30 control and data signals
    wire wrProc30East;
    wire fullProc30East;
    wire [31:0] dataOutProc30East;

     //Processor 31 control and data signals
    wire wrProc31North;
    wire fullProc31North;
    wire [31:0] dataOutProc31North;

     //Processor 31 control and data signals
    wire rdProc31South;
    wire emptyProc31South;
    wire [31:0] dataInProc31South;

     //Processor 31 control and data signals
    wire wrProc31South;
    wire fullProc31South;
    wire [31:0] dataOutProc31South;

     //Processor 31 control and data signals
    wire rdProc31East;
    wire emptyProc31East;
    wire [31:0] dataInProc31East;

     //Processor 31 control and data signals
    wire rdProc31West;
    wire emptyProc31West;
    wire [31:0] dataInProc31West;

     //Processor 32 control and data signals
    wire wrProc32North;
    wire fullProc32North;
    wire [31:0] dataOutProc32North;

     //Processor 32 control and data signals
    wire rdProc32South;
    wire emptyProc32South;
    wire [31:0] dataInProc32South;

     //Processor 32 control and data signals
    wire wrProc32East;
    wire fullProc32East;
    wire [31:0] dataOutProc32East;

     //Processor 32 control and data signals
    wire wrProc32West;
    wire fullProc32West;
    wire [31:0] dataOutProc32West;

     //Processor 33 control and data signals
    wire wrProc33North;
    wire fullProc33North;
    wire [31:0] dataOutProc33North;

     //Processor 33 control and data signals
    wire rdProc33West;
    wire emptyProc33West;
    wire [31:0] dataInProc33West;

     //Processor 34 control and data signals
    wire rdProc34North;
    wire emptyProc34North;
    wire [31:0] dataInProc34North;

     //Processor 34 control and data signals
    wire wrProc34South;
    wire fullProc34South;
    wire [31:0] dataOutProc34South;

     //Processor 35 control and data signals
    wire rdProc35North;
    wire emptyProc35North;
    wire [31:0] dataInProc35North;

     //Processor 35 control and data signals
    wire wrProc35South;
    wire fullProc35South;
    wire [31:0] dataOutProc35South;

     //Processor 35 control and data signals
    wire wrProc35East;
    wire fullProc35East;
    wire [31:0] dataOutProc35East;

     //Processor 36 control and data signals
    wire rdProc36North;
    wire emptyProc36North;
    wire [31:0] dataInProc36North;

     //Processor 36 control and data signals
    wire wrProc36North;
    wire fullProc36North;
    wire [31:0] dataOutProc36North;

     //Processor 36 control and data signals
    wire wrProc36South;
    wire fullProc36South;
    wire [31:0] dataOutProc36South;

     //Processor 36 control and data signals
    wire rdProc36East;
    wire emptyProc36East;
    wire [31:0] dataInProc36East;

     //Processor 36 control and data signals
    wire wrProc36East;
    wire fullProc36East;
    wire [31:0] dataOutProc36East;

     //Processor 36 control and data signals
    wire rdProc36West;
    wire emptyProc36West;
    wire [31:0] dataInProc36West;

     //Processor 37 control and data signals
    wire wrProc37North;
    wire fullProc37North;
    wire [31:0] dataOutProc37North;

     //Processor 37 control and data signals
    wire wrProc37South;
    wire fullProc37South;
    wire [31:0] dataOutProc37South;

     //Processor 37 control and data signals
    wire rdProc37East;
    wire emptyProc37East;
    wire [31:0] dataInProc37East;

     //Processor 37 control and data signals
    wire rdProc37West;
    wire emptyProc37West;
    wire [31:0] dataInProc37West;

     //Processor 37 control and data signals
    wire wrProc37West;
    wire fullProc37West;
    wire [31:0] dataOutProc37West;

     //Processor 38 control and data signals
    wire rdProc38South;
    wire emptyProc38South;
    wire [31:0] dataInProc38South;

     //Processor 38 control and data signals
    wire rdProc38East;
    wire emptyProc38East;
    wire [31:0] dataInProc38East;

     //Processor 38 control and data signals
    wire wrProc38East;
    wire fullProc38East;
    wire [31:0] dataOutProc38East;

     //Processor 38 control and data signals
    wire wrProc38West;
    wire fullProc38West;
    wire [31:0] dataOutProc38West;

     //Processor 39 control and data signals
    wire rdProc39West;
    wire emptyProc39West;
    wire [31:0] dataInProc39West;

     //Processor 39 control and data signals
    wire wrProc39West;
    wire fullProc39West;
    wire [31:0] dataOutProc39West;

     //Processor 40 control and data signals
    wire rdProc40North;
    wire emptyProc40North;
    wire [31:0] dataInProc40North;

     //Processor 40 control and data signals
    wire wrProc40East;
    wire fullProc40East;
    wire [31:0] dataOutProc40East;

     //Processor 41 control and data signals
    wire rdProc41North;
    wire emptyProc41North;
    wire [31:0] dataInProc41North;

     //Processor 41 control and data signals
    wire wrProc41North;
    wire fullProc41North;
    wire [31:0] dataOutProc41North;

     //Processor 41 control and data signals
    wire wrProc41East;
    wire fullProc41East;
    wire [31:0] dataOutProc41East;

     //Processor 41 control and data signals
    wire rdProc41West;
    wire emptyProc41West;
    wire [31:0] dataInProc41West;

     //Processor 42 control and data signals
    wire wrProc42North;
    wire fullProc42North;
    wire [31:0] dataOutProc42North;

     //Processor 42 control and data signals
    wire rdProc42East;
    wire emptyProc42East;
    wire [31:0] dataInProc42East;

     //Processor 42 control and data signals
    wire rdProc42West;
    wire emptyProc42West;
    wire [31:0] dataInProc42West;

     //Processor 43 control and data signals
    wire rdProc43East;
    wire emptyProc43East;
    wire [31:0] dataInProc43East;

     //Processor 43 control and data signals
    wire wrProc43West;
    wire fullProc43West;
    wire [31:0] dataOutProc43West;

     //Processor 44 control and data signals
    wire rdProc44North;
    wire emptyProc44North;
    wire [31:0] dataInProc44North;

     //Processor 44 control and data signals
    wire rdProc44East;
    wire emptyProc44East;
    wire [31:0] dataInProc44East;

     //Processor 44 control and data signals
    wire wrProc44West;
    wire fullProc44West;
    wire [31:0] dataOutProc44West;

     //Processor 45 control and data signals
    wire rdProc45North;
    wire emptyProc45North;
    wire [31:0] dataInProc45North;

     //Processor 45 control and data signals
    wire wrProc45West;
    wire fullProc45West;
    wire [31:0] dataOutProc45West;

     //Processor 46 control and data signals
    wire rdProc46North;
    wire emptyProc46North;
    wire [31:0] dataInProc46North;

     //Processor 46 control and data signals
    wire wrProc46East;
    wire fullProc46East;
    wire [31:0] dataOutProc46East;

     //Processor 47 control and data signals
    wire rdProc47North;
    wire emptyProc47North;
    wire [31:0] dataInProc47North;

     //Processor 47 control and data signals
    wire wrProc47East;
    wire fullProc47East;
    wire [31:0] dataOutProc47East;

     //Processor 47 control and data signals
    wire rdProc47West;
    wire emptyProc47West;
    wire [31:0] dataInProc47West;

     //Processor 48 control and data signals
    wire wrProc48North;
    wire fullProc48North;
    wire [31:0] dataOutProc48North;

     //Processor 48 control and data signals
    wire rdProc48East;
    wire emptyProc48East;
    wire [31:0] dataInProc48East;

     //Processor 48 control and data signals
    wire wrProc48East;
    wire fullProc48East;
    wire [31:0] dataOutProc48East;

     //Processor 48 control and data signals
    wire rdProc48West;
    wire emptyProc48West;
    wire [31:0] dataInProc48West;

     //Processor 49 control and data signals
    wire rdProc49West;
    wire emptyProc49West;
    wire [31:0] dataInProc49West;

     //Processor 49 control and data signals
    wire wrProc49West;
    wire fullProc49West;
    wire [31:0] dataOutProc49West;



//PROCESSOR 0
system proc0(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe0),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe0),
    .wrSouth(wrProc0South),
    .fullSouth(fullProc0South),
    .dataOutSouth(dataOutProc0South),
    .rdEast(rdProc0East),
    .emptyEast(emptyProc0East),
    .dataInEast(dataInProc0East),
    .wrEast(wrProc0East),
    .fullEast(fullProc0East),
    .dataOutEast(dataOutProc0East));

//PROCESSOR 1
system proc1(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe1),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe1),
    .rdWest(rdProc1West),
    .emptyWest(emptyProc1West),
    .dataInWest(dataInProc1West),
    .wrWest(wrProc1West),
    .fullWest(fullProc1West),
    .dataOutWest(dataOutProc1West));

//PROCESSOR 2
system proc2(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe2),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe2),
    .rdEast(rdProc2East),
    .emptyEast(emptyProc2East),
    .dataInEast(dataInProc2East),
    .reg_file_b_readdataout(reg_file_b_readdataout));

//PROCESSOR 3
system proc3(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe3),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe3),
    .rdEast(rdProc3East),
    .emptyEast(emptyProc3East),
    .dataInEast(dataInProc3East),
    .wrWest(wrProc3West),
    .fullWest(fullProc3West),
    .dataOutWest(dataOutProc3West));

//PROCESSOR 4
system proc4(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe4),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe4),
    .rdEast(rdProc4East),
    .emptyEast(emptyProc4East),
    .dataInEast(dataInProc4East),
    .wrWest(wrProc4West),
    .fullWest(fullProc4West),
    .dataOutWest(dataOutProc4West));

//PROCESSOR 5
system proc5(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe5),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe5),
    .rdEast(rdProc5East),
    .emptyEast(emptyProc5East),
    .dataInEast(dataInProc5East),
    .wrWest(wrProc5West),
    .fullWest(fullProc5West),
    .dataOutWest(dataOutProc5West));

//PROCESSOR 6
system proc6(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe6),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe6),
    .rdSouth(rdProc6South),
    .emptySouth(emptyProc6South),
    .dataInSouth(dataInProc6South),
    .wrSouth(wrProc6South),
    .fullSouth(fullProc6South),
    .dataOutSouth(dataOutProc6South),
    .rdEast(rdProc6East),
    .emptyEast(emptyProc6East),
    .dataInEast(dataInProc6East),
    .wrWest(wrProc6West),
    .fullWest(fullProc6West),
    .dataOutWest(dataOutProc6West));

//PROCESSOR 7
system proc7(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe7),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe7),
    .wrSouth(wrProc7South),
    .fullSouth(fullProc7South),
    .dataOutSouth(dataOutProc7South),
    .rdEast(rdProc7East),
    .emptyEast(emptyProc7East),
    .dataInEast(dataInProc7East),
    .wrWest(wrProc7West),
    .fullWest(fullProc7West),
    .dataOutWest(dataOutProc7West));

//PROCESSOR 8
system proc8(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe8),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe8),
    .rdSouth(rdProc8South),
    .emptySouth(emptyProc8South),
    .dataInSouth(dataInProc8South),
    .rdEast(rdProc8East),
    .emptyEast(emptyProc8East),
    .dataInEast(dataInProc8East),
    .wrWest(wrProc8West),
    .fullWest(fullProc8West),
    .dataOutWest(dataOutProc8West));

//PROCESSOR 9
system proc9(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe9),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe9),
    .rdSouth(rdProc9South),
    .emptySouth(emptyProc9South),
    .dataInSouth(dataInProc9South),
    .wrWest(wrProc9West),
    .fullWest(fullProc9West),
    .dataOutWest(dataOutProc9West));

//PROCESSOR 10
system proc10(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe10),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe10),
    .rdNorth(rdProc10North),
    .emptyNorth(emptyProc10North),
    .dataInNorth(dataInProc10North),
    .wrSouth(wrProc10South),
    .fullSouth(fullProc10South),
    .dataOutSouth(dataOutProc10South));

//PROCESSOR 11
system proc11(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe11),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe11),
    .rdSouth(rdProc11South),
    .emptySouth(emptyProc11South),
    .dataInSouth(dataInProc11South),
    .wrEast(wrProc11East),
    .fullEast(fullProc11East),
    .dataOutEast(dataOutProc11East));

//PROCESSOR 12
system proc12(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe12),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe12),
    .rdSouth(rdProc12South),
    .emptySouth(emptyProc12South),
    .dataInSouth(dataInProc12South),
    .wrSouth(wrProc12South),
    .fullSouth(fullProc12South),
    .dataOutSouth(dataOutProc12South),
    .wrEast(wrProc12East),
    .fullEast(fullProc12East),
    .dataOutEast(dataOutProc12East),
    .rdWest(rdProc12West),
    .emptyWest(emptyProc12West),
    .dataInWest(dataInProc12West));

//PROCESSOR 13
system proc13(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe13),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe13),
    .wrEast(wrProc13East),
    .fullEast(fullProc13East),
    .dataOutEast(dataOutProc13East),
    .rdWest(rdProc13West),
    .emptyWest(emptyProc13West),
    .dataInWest(dataInProc13West));

//PROCESSOR 14
system proc14(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe14),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe14),
    .rdSouth(rdProc14South),
    .emptySouth(emptyProc14South),
    .dataInSouth(dataInProc14South),
    .wrSouth(wrProc14South),
    .fullSouth(fullProc14South),
    .dataOutSouth(dataOutProc14South),
    .rdEast(rdProc14East),
    .emptyEast(emptyProc14East),
    .dataInEast(dataInProc14East),
    .wrEast(wrProc14East),
    .fullEast(fullProc14East),
    .dataOutEast(dataOutProc14East),
    .rdWest(rdProc14West),
    .emptyWest(emptyProc14West),
    .dataInWest(dataInProc14West));

//PROCESSOR 15
system proc15(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe15),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe15),
    .wrSouth(wrProc15South),
    .fullSouth(fullProc15South),
    .dataOutSouth(dataOutProc15South),
    .rdEast(rdProc15East),
    .emptyEast(emptyProc15East),
    .dataInEast(dataInProc15East),
    .wrEast(wrProc15East),
    .fullEast(fullProc15East),
    .dataOutEast(dataOutProc15East),
    .rdWest(rdProc15West),
    .emptyWest(emptyProc15West),
    .dataInWest(dataInProc15West),
    .wrWest(wrProc15West),
    .fullWest(fullProc15West),
    .dataOutWest(dataOutProc15West));

//PROCESSOR 16
system proc16(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe16),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe16),
    .rdNorth(rdProc16North),
    .emptyNorth(emptyProc16North),
    .dataInNorth(dataInProc16North),
    .wrNorth(wrProc16North),
    .fullNorth(fullProc16North),
    .dataOutNorth(dataOutProc16North),
    .rdSouth(rdProc16South),
    .emptySouth(emptyProc16South),
    .dataInSouth(dataInProc16South),
    .wrSouth(wrProc16South),
    .fullSouth(fullProc16South),
    .dataOutSouth(dataOutProc16South),
    .rdEast(rdProc16East),
    .emptyEast(emptyProc16East),
    .dataInEast(dataInProc16East),
    .rdWest(rdProc16West),
    .emptyWest(emptyProc16West),
    .dataInWest(dataInProc16West),
    .wrWest(wrProc16West),
    .fullWest(fullProc16West),
    .dataOutWest(dataOutProc16West));

//PROCESSOR 17
system proc17(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe17),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe17),
    .rdNorth(rdProc17North),
    .emptyNorth(emptyProc17North),
    .dataInNorth(dataInProc17North),
    .wrWest(wrProc17West),
    .fullWest(fullProc17West),
    .dataOutWest(dataOutProc17West));

//PROCESSOR 18
system proc18(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe18),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe18),
    .wrNorth(wrProc18North),
    .fullNorth(fullProc18North),
    .dataOutNorth(dataOutProc18North),
    .rdSouth(rdProc18South),
    .emptySouth(emptyProc18South),
    .dataInSouth(dataInProc18South),
    .rdEast(rdProc18East),
    .emptyEast(emptyProc18East),
    .dataInEast(dataInProc18East),
    .wrEast(wrProc18East),
    .fullEast(fullProc18East),
    .dataOutEast(dataOutProc18East));

//PROCESSOR 19
system proc19(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe19),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe19),
    .wrNorth(wrProc19North),
    .fullNorth(fullProc19North),
    .dataOutNorth(dataOutProc19North),
    .rdSouth(rdProc19South),
    .emptySouth(emptyProc19South),
    .dataInSouth(dataInProc19South),
    .rdWest(rdProc19West),
    .emptyWest(emptyProc19West),
    .dataInWest(dataInProc19West),
    .wrWest(wrProc19West),
    .fullWest(fullProc19West),
    .dataOutWest(dataOutProc19West));

//PROCESSOR 20
system proc20(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe20),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe20),
    .rdNorth(rdProc20North),
    .emptyNorth(emptyProc20North),
    .dataInNorth(dataInProc20North),
    .wrSouth(wrProc20South),
    .fullSouth(fullProc20South),
    .dataOutSouth(dataOutProc20South));

//PROCESSOR 21
system proc21(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe21),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe21),
    .wrNorth(wrProc21North),
    .fullNorth(fullProc21North),
    .dataOutNorth(dataOutProc21North),
    .rdSouth(rdProc21South),
    .emptySouth(emptyProc21South),
    .dataInSouth(dataInProc21South),
    .wrEast(wrProc21East),
    .fullEast(fullProc21East),
    .dataOutEast(dataOutProc21East));

//PROCESSOR 22
system proc22(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe22),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe22),
    .rdNorth(rdProc22North),
    .emptyNorth(emptyProc22North),
    .dataInNorth(dataInProc22North),
    .wrNorth(wrProc22North),
    .fullNorth(fullProc22North),
    .dataOutNorth(dataOutProc22North),
    .rdSouth(rdProc22South),
    .emptySouth(emptyProc22South),
    .dataInSouth(dataInProc22South),
    .wrEast(wrProc22East),
    .fullEast(fullProc22East),
    .dataOutEast(dataOutProc22East),
    .rdWest(rdProc22West),
    .emptyWest(emptyProc22West),
    .dataInWest(dataInProc22West));

//PROCESSOR 23
system proc23(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe23),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe23),
    .rdSouth(rdProc23South),
    .emptySouth(emptyProc23South),
    .dataInSouth(dataInProc23South),
    .wrEast(wrProc23East),
    .fullEast(fullProc23East),
    .dataOutEast(dataOutProc23East),
    .rdWest(rdProc23West),
    .emptyWest(emptyProc23West),
    .dataInWest(dataInProc23West));

//PROCESSOR 24
system proc24(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe24),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe24),
    .rdNorth(rdProc24North),
    .emptyNorth(emptyProc24North),
    .dataInNorth(dataInProc24North),
    .wrNorth(wrProc24North),
    .fullNorth(fullProc24North),
    .dataOutNorth(dataOutProc24North),
    .wrSouth(wrProc24South),
    .fullSouth(fullProc24South),
    .dataOutSouth(dataOutProc24South),
    .wrEast(wrProc24East),
    .fullEast(fullProc24East),
    .dataOutEast(dataOutProc24East),
    .rdWest(rdProc24West),
    .emptyWest(emptyProc24West),
    .dataInWest(dataInProc24West));

//PROCESSOR 25
system proc25(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe25),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe25),
    .rdNorth(rdProc25North),
    .emptyNorth(emptyProc25North),
    .dataInNorth(dataInProc25North),
    .wrSouth(wrProc25South),
    .fullSouth(fullProc25South),
    .dataOutSouth(dataOutProc25South),
    .wrEast(wrProc25East),
    .fullEast(fullProc25East),
    .dataOutEast(dataOutProc25East),
    .rdWest(rdProc25West),
    .emptyWest(emptyProc25West),
    .dataInWest(dataInProc25West));

//PROCESSOR 26
system proc26(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe26),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe26),
    .rdNorth(rdProc26North),
    .emptyNorth(emptyProc26North),
    .dataInNorth(dataInProc26North),
    .wrNorth(wrProc26North),
    .fullNorth(fullProc26North),
    .dataOutNorth(dataOutProc26North),
    .rdSouth(rdProc26South),
    .emptySouth(emptyProc26South),
    .dataInSouth(dataInProc26South),
    .wrSouth(wrProc26South),
    .fullSouth(fullProc26South),
    .dataOutSouth(dataOutProc26South),
    .rdEast(rdProc26East),
    .emptyEast(emptyProc26East),
    .dataInEast(dataInProc26East),
    .wrEast(wrProc26East),
    .fullEast(fullProc26East),
    .dataOutEast(dataOutProc26East),
    .rdWest(rdProc26West),
    .emptyWest(emptyProc26West),
    .dataInWest(dataInProc26West));

//PROCESSOR 27
system proc27(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe27),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe27),
    .rdSouth(rdProc27South),
    .emptySouth(emptyProc27South),
    .dataInSouth(dataInProc27South),
    .wrEast(wrProc27East),
    .fullEast(fullProc27East),
    .dataOutEast(dataOutProc27East),
    .rdWest(rdProc27West),
    .emptyWest(emptyProc27West),
    .dataInWest(dataInProc27West),
    .wrWest(wrProc27West),
    .fullWest(fullProc27West),
    .dataOutWest(dataOutProc27West));

//PROCESSOR 28
system proc28(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe28),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe28),
    .wrNorth(wrProc28North),
    .fullNorth(fullProc28North),
    .dataOutNorth(dataOutProc28North),
    .wrEast(wrProc28East),
    .fullEast(fullProc28East),
    .dataOutEast(dataOutProc28East),
    .rdWest(rdProc28West),
    .emptyWest(emptyProc28West),
    .dataInWest(dataInProc28West));

//PROCESSOR 29
system proc29(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe29),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe29),
    .wrNorth(wrProc29North),
    .fullNorth(fullProc29North),
    .dataOutNorth(dataOutProc29North),
    .rdWest(rdProc29West),
    .emptyWest(emptyProc29West),
    .dataInWest(dataInProc29West));

//PROCESSOR 30
system proc30(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe30),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe30),
    .rdNorth(rdProc30North),
    .emptyNorth(emptyProc30North),
    .dataInNorth(dataInProc30North),
    .wrSouth(wrProc30South),
    .fullSouth(fullProc30South),
    .dataOutSouth(dataOutProc30South),
    .wrEast(wrProc30East),
    .fullEast(fullProc30East),
    .dataOutEast(dataOutProc30East));

//PROCESSOR 31
system proc31(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe31),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe31),
    .wrNorth(wrProc31North),
    .fullNorth(fullProc31North),
    .dataOutNorth(dataOutProc31North),
    .rdSouth(rdProc31South),
    .emptySouth(emptyProc31South),
    .dataInSouth(dataInProc31South),
    .wrSouth(wrProc31South),
    .fullSouth(fullProc31South),
    .dataOutSouth(dataOutProc31South),
    .rdEast(rdProc31East),
    .emptyEast(emptyProc31East),
    .dataInEast(dataInProc31East),
    .rdWest(rdProc31West),
    .emptyWest(emptyProc31West),
    .dataInWest(dataInProc31West));

//PROCESSOR 32
system proc32(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe32),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe32),
    .wrNorth(wrProc32North),
    .fullNorth(fullProc32North),
    .dataOutNorth(dataOutProc32North),
    .rdSouth(rdProc32South),
    .emptySouth(emptyProc32South),
    .dataInSouth(dataInProc32South),
    .wrEast(wrProc32East),
    .fullEast(fullProc32East),
    .dataOutEast(dataOutProc32East),
    .wrWest(wrProc32West),
    .fullWest(fullProc32West),
    .dataOutWest(dataOutProc32West));

//PROCESSOR 33
system proc33(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe33),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe33),
    .wrNorth(wrProc33North),
    .fullNorth(fullProc33North),
    .dataOutNorth(dataOutProc33North),
    .rdWest(rdProc33West),
    .emptyWest(emptyProc33West),
    .dataInWest(dataInProc33West));

//PROCESSOR 34
system proc34(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe34),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe34),
    .rdNorth(rdProc34North),
    .emptyNorth(emptyProc34North),
    .dataInNorth(dataInProc34North),
    .wrSouth(wrProc34South),
    .fullSouth(fullProc34South),
    .dataOutSouth(dataOutProc34South));

//PROCESSOR 35
system proc35(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe35),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe35),
    .rdNorth(rdProc35North),
    .emptyNorth(emptyProc35North),
    .dataInNorth(dataInProc35North),
    .wrSouth(wrProc35South),
    .fullSouth(fullProc35South),
    .dataOutSouth(dataOutProc35South),
    .wrEast(wrProc35East),
    .fullEast(fullProc35East),
    .dataOutEast(dataOutProc35East));

//PROCESSOR 36
system proc36(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe36),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe36),
    .rdNorth(rdProc36North),
    .emptyNorth(emptyProc36North),
    .dataInNorth(dataInProc36North),
    .wrNorth(wrProc36North),
    .fullNorth(fullProc36North),
    .dataOutNorth(dataOutProc36North),
    .wrSouth(wrProc36South),
    .fullSouth(fullProc36South),
    .dataOutSouth(dataOutProc36South),
    .rdEast(rdProc36East),
    .emptyEast(emptyProc36East),
    .dataInEast(dataInProc36East),
    .wrEast(wrProc36East),
    .fullEast(fullProc36East),
    .dataOutEast(dataOutProc36East),
    .rdWest(rdProc36West),
    .emptyWest(emptyProc36West),
    .dataInWest(dataInProc36West));

//PROCESSOR 37
system proc37(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe37),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe37),
    .wrNorth(wrProc37North),
    .fullNorth(fullProc37North),
    .dataOutNorth(dataOutProc37North),
    .wrSouth(wrProc37South),
    .fullSouth(fullProc37South),
    .dataOutSouth(dataOutProc37South),
    .rdEast(rdProc37East),
    .emptyEast(emptyProc37East),
    .dataInEast(dataInProc37East),
    .rdWest(rdProc37West),
    .emptyWest(emptyProc37West),
    .dataInWest(dataInProc37West),
    .wrWest(wrProc37West),
    .fullWest(fullProc37West),
    .dataOutWest(dataOutProc37West));

//PROCESSOR 38
system proc38(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe38),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe38),
    .rdSouth(rdProc38South),
    .emptySouth(emptyProc38South),
    .dataInSouth(dataInProc38South),
    .rdEast(rdProc38East),
    .emptyEast(emptyProc38East),
    .dataInEast(dataInProc38East),
    .wrEast(wrProc38East),
    .fullEast(fullProc38East),
    .dataOutEast(dataOutProc38East),
    .wrWest(wrProc38West),
    .fullWest(fullProc38West),
    .dataOutWest(dataOutProc38West));

//PROCESSOR 39
system proc39(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe39),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe39),
    .rdWest(rdProc39West),
    .emptyWest(emptyProc39West),
    .dataInWest(dataInProc39West),
    .wrWest(wrProc39West),
    .fullWest(fullProc39West),
    .dataOutWest(dataOutProc39West));

//PROCESSOR 40
system proc40(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe40),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe40),
    .rdNorth(rdProc40North),
    .emptyNorth(emptyProc40North),
    .dataInNorth(dataInProc40North),
    .wrEast(wrProc40East),
    .fullEast(fullProc40East),
    .dataOutEast(dataOutProc40East));

//PROCESSOR 41
system proc41(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe41),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe41),
    .rdNorth(rdProc41North),
    .emptyNorth(emptyProc41North),
    .dataInNorth(dataInProc41North),
    .wrNorth(wrProc41North),
    .fullNorth(fullProc41North),
    .dataOutNorth(dataOutProc41North),
    .wrEast(wrProc41East),
    .fullEast(fullProc41East),
    .dataOutEast(dataOutProc41East),
    .rdWest(rdProc41West),
    .emptyWest(emptyProc41West),
    .dataInWest(dataInProc41West));

//PROCESSOR 42
system proc42(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe42),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe42),
    .wrNorth(wrProc42North),
    .fullNorth(fullProc42North),
    .dataOutNorth(dataOutProc42North),
    .rdEast(rdProc42East),
    .emptyEast(emptyProc42East),
    .dataInEast(dataInProc42East),
    .rdWest(rdProc42West),
    .emptyWest(emptyProc42West),
    .dataInWest(dataInProc42West));

//PROCESSOR 43
system proc43(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe43),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe43),
    .rdEast(rdProc43East),
    .emptyEast(emptyProc43East),
    .dataInEast(dataInProc43East),
    .wrWest(wrProc43West),
    .fullWest(fullProc43West),
    .dataOutWest(dataOutProc43West));

//PROCESSOR 44
system proc44(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe44),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe44),
    .rdNorth(rdProc44North),
    .emptyNorth(emptyProc44North),
    .dataInNorth(dataInProc44North),
    .rdEast(rdProc44East),
    .emptyEast(emptyProc44East),
    .dataInEast(dataInProc44East),
    .wrWest(wrProc44West),
    .fullWest(fullProc44West),
    .dataOutWest(dataOutProc44West));

//PROCESSOR 45
system proc45(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe45),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe45),
    .rdNorth(rdProc45North),
    .emptyNorth(emptyProc45North),
    .dataInNorth(dataInProc45North),
    .wrWest(wrProc45West),
    .fullWest(fullProc45West),
    .dataOutWest(dataOutProc45West));

//PROCESSOR 46
system proc46(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe46),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe46),
    .rdNorth(rdProc46North),
    .emptyNorth(emptyProc46North),
    .dataInNorth(dataInProc46North),
    .wrEast(wrProc46East),
    .fullEast(fullProc46East),
    .dataOutEast(dataOutProc46East));

//PROCESSOR 47
system proc47(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe47),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe47),
    .rdNorth(rdProc47North),
    .emptyNorth(emptyProc47North),
    .dataInNorth(dataInProc47North),
    .wrEast(wrProc47East),
    .fullEast(fullProc47East),
    .dataOutEast(dataOutProc47East),
    .rdWest(rdProc47West),
    .emptyWest(emptyProc47West),
    .dataInWest(dataInProc47West));

//PROCESSOR 48
system proc48(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe48),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe48),
    .wrNorth(wrProc48North),
    .fullNorth(fullProc48North),
    .dataOutNorth(dataOutProc48North),
    .rdEast(rdProc48East),
    .emptyEast(emptyProc48East),
    .dataInEast(dataInProc48East),
    .wrEast(wrProc48East),
    .fullEast(fullProc48East),
    .dataOutEast(dataOutProc48East),
    .rdWest(rdProc48West),
    .emptyWest(emptyProc48West),
    .dataInWest(dataInProc48West));

//PROCESSOR 49
system proc49(.clk(clk),
    .resetn (resetn),
    .boot_iaddr(boot_iaddr),
    .boot_idata(boot_idata),
    .boot_iwe(boot_iwe49),
    .boot_daddr(boot_daddr),
    .boot_ddata(boot_ddata),
    .boot_dwe(boot_dwe49),
    .rdWest(rdProc49West),
    .emptyWest(emptyProc49West),
    .dataInWest(dataInProc49West),
    .wrWest(wrProc49West),
    .fullWest(fullProc49West),
    .dataOutWest(dataOutProc49West));

//FIFO 0 TO 10
fifo fifo_proc0_to_proc10(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc0South),
    .full(fullProc0South),
    .dataIn(dataOutProc0South),
    .rd(rdProc10North),
    .empty(emptyProc10North),
    .dataOut(dataInProc10North));

//FIFO 1 TO 0
fifo fifo_proc1_to_proc0(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc1West),
    .full(fullProc1West),
    .dataIn(dataOutProc1West),
    .rd(rdProc0East),
    .empty(emptyProc0East),
    .dataOut(dataInProc0East));

//FIFO 0 TO 1
fifo fifo_proc0_to_proc1(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc0East),
    .full(fullProc0East),
    .dataIn(dataOutProc0East),
    .rd(rdProc1West),
    .empty(emptyProc1West),
    .dataOut(dataInProc1West));

//FIFO 3 TO 2
fifo fifo_proc3_to_proc2(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc3West),
    .full(fullProc3West),
    .dataIn(dataOutProc3West),
    .rd(rdProc2East),
    .empty(emptyProc2East),
    .dataOut(dataInProc2East));

//FIFO 4 TO 3
fifo fifo_proc4_to_proc3(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc4West),
    .full(fullProc4West),
    .dataIn(dataOutProc4West),
    .rd(rdProc3East),
    .empty(emptyProc3East),
    .dataOut(dataInProc3East));

//FIFO 5 TO 4
fifo fifo_proc5_to_proc4(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc5West),
    .full(fullProc5West),
    .dataIn(dataOutProc5West),
    .rd(rdProc4East),
    .empty(emptyProc4East),
    .dataOut(dataInProc4East));

//FIFO 6 TO 5
fifo fifo_proc6_to_proc5(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc6West),
    .full(fullProc6West),
    .dataIn(dataOutProc6West),
    .rd(rdProc5East),
    .empty(emptyProc5East),
    .dataOut(dataInProc5East));

//FIFO 16 TO 6
fifo fifo_proc16_to_proc6(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc16North),
    .full(fullProc16North),
    .dataIn(dataOutProc16North),
    .rd(rdProc6South),
    .empty(emptyProc6South),
    .dataOut(dataInProc6South));

//FIFO 6 TO 16
fifo fifo_proc6_to_proc16(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc6South),
    .full(fullProc6South),
    .dataIn(dataOutProc6South),
    .rd(rdProc16North),
    .empty(emptyProc16North),
    .dataOut(dataInProc16North));

//FIFO 7 TO 6
fifo fifo_proc7_to_proc6(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc7West),
    .full(fullProc7West),
    .dataIn(dataOutProc7West),
    .rd(rdProc6East),
    .empty(emptyProc6East),
    .dataOut(dataInProc6East));

//FIFO 7 TO 17
fifo fifo_proc7_to_proc17(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc7South),
    .full(fullProc7South),
    .dataIn(dataOutProc7South),
    .rd(rdProc17North),
    .empty(emptyProc17North),
    .dataOut(dataInProc17North));

//FIFO 8 TO 7
fifo fifo_proc8_to_proc7(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc8West),
    .full(fullProc8West),
    .dataIn(dataOutProc8West),
    .rd(rdProc7East),
    .empty(emptyProc7East),
    .dataOut(dataInProc7East));

//FIFO 18 TO 8
fifo fifo_proc18_to_proc8(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc18North),
    .full(fullProc18North),
    .dataIn(dataOutProc18North),
    .rd(rdProc8South),
    .empty(emptyProc8South),
    .dataOut(dataInProc8South));

//FIFO 9 TO 8
fifo fifo_proc9_to_proc8(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc9West),
    .full(fullProc9West),
    .dataIn(dataOutProc9West),
    .rd(rdProc8East),
    .empty(emptyProc8East),
    .dataOut(dataInProc8East));

//FIFO 19 TO 9
fifo fifo_proc19_to_proc9(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc19North),
    .full(fullProc19North),
    .dataIn(dataOutProc19North),
    .rd(rdProc9South),
    .empty(emptyProc9South),
    .dataOut(dataInProc9South));

//FIFO 10 TO 20
fifo fifo_proc10_to_proc20(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc10South),
    .full(fullProc10South),
    .dataIn(dataOutProc10South),
    .rd(rdProc20North),
    .empty(emptyProc20North),
    .dataOut(dataInProc20North));

//FIFO 21 TO 11
fifo fifo_proc21_to_proc11(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc21North),
    .full(fullProc21North),
    .dataIn(dataOutProc21North),
    .rd(rdProc11South),
    .empty(emptyProc11South),
    .dataOut(dataInProc11South));

//FIFO 11 TO 12
fifo fifo_proc11_to_proc12(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc11East),
    .full(fullProc11East),
    .dataIn(dataOutProc11East),
    .rd(rdProc12West),
    .empty(emptyProc12West),
    .dataOut(dataInProc12West));

//FIFO 22 TO 12
fifo fifo_proc22_to_proc12(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc22North),
    .full(fullProc22North),
    .dataIn(dataOutProc22North),
    .rd(rdProc12South),
    .empty(emptyProc12South),
    .dataOut(dataInProc12South));

//FIFO 12 TO 22
fifo fifo_proc12_to_proc22(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc12South),
    .full(fullProc12South),
    .dataIn(dataOutProc12South),
    .rd(rdProc22North),
    .empty(emptyProc22North),
    .dataOut(dataInProc22North));

//FIFO 12 TO 13
fifo fifo_proc12_to_proc13(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc12East),
    .full(fullProc12East),
    .dataIn(dataOutProc12East),
    .rd(rdProc13West),
    .empty(emptyProc13West),
    .dataOut(dataInProc13West));

//FIFO 13 TO 14
fifo fifo_proc13_to_proc14(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc13East),
    .full(fullProc13East),
    .dataIn(dataOutProc13East),
    .rd(rdProc14West),
    .empty(emptyProc14West),
    .dataOut(dataInProc14West));

//FIFO 24 TO 14
fifo fifo_proc24_to_proc14(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc24North),
    .full(fullProc24North),
    .dataIn(dataOutProc24North),
    .rd(rdProc14South),
    .empty(emptyProc14South),
    .dataOut(dataInProc14South));

//FIFO 14 TO 24
fifo fifo_proc14_to_proc24(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc14South),
    .full(fullProc14South),
    .dataIn(dataOutProc14South),
    .rd(rdProc24North),
    .empty(emptyProc24North),
    .dataOut(dataInProc24North));

//FIFO 15 TO 14
fifo fifo_proc15_to_proc14(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc15West),
    .full(fullProc15West),
    .dataIn(dataOutProc15West),
    .rd(rdProc14East),
    .empty(emptyProc14East),
    .dataOut(dataInProc14East));

//FIFO 14 TO 15
fifo fifo_proc14_to_proc15(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc14East),
    .full(fullProc14East),
    .dataIn(dataOutProc14East),
    .rd(rdProc15West),
    .empty(emptyProc15West),
    .dataOut(dataInProc15West));

//FIFO 15 TO 25
fifo fifo_proc15_to_proc25(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc15South),
    .full(fullProc15South),
    .dataIn(dataOutProc15South),
    .rd(rdProc25North),
    .empty(emptyProc25North),
    .dataOut(dataInProc25North));

//FIFO 16 TO 15
fifo fifo_proc16_to_proc15(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc16West),
    .full(fullProc16West),
    .dataIn(dataOutProc16West),
    .rd(rdProc15East),
    .empty(emptyProc15East),
    .dataOut(dataInProc15East));

//FIFO 15 TO 16
fifo fifo_proc15_to_proc16(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc15East),
    .full(fullProc15East),
    .dataIn(dataOutProc15East),
    .rd(rdProc16West),
    .empty(emptyProc16West),
    .dataOut(dataInProc16West));

//FIFO 26 TO 16
fifo fifo_proc26_to_proc16(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc26North),
    .full(fullProc26North),
    .dataIn(dataOutProc26North),
    .rd(rdProc16South),
    .empty(emptyProc16South),
    .dataOut(dataInProc16South));

//FIFO 16 TO 26
fifo fifo_proc16_to_proc26(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc16South),
    .full(fullProc16South),
    .dataIn(dataOutProc16South),
    .rd(rdProc26North),
    .empty(emptyProc26North),
    .dataOut(dataInProc26North));

//FIFO 17 TO 16
fifo fifo_proc17_to_proc16(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc17West),
    .full(fullProc17West),
    .dataIn(dataOutProc17West),
    .rd(rdProc16East),
    .empty(emptyProc16East),
    .dataOut(dataInProc16East));

//FIFO 28 TO 18
fifo fifo_proc28_to_proc18(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc28North),
    .full(fullProc28North),
    .dataIn(dataOutProc28North),
    .rd(rdProc18South),
    .empty(emptyProc18South),
    .dataOut(dataInProc18South));

//FIFO 19 TO 18
fifo fifo_proc19_to_proc18(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc19West),
    .full(fullProc19West),
    .dataIn(dataOutProc19West),
    .rd(rdProc18East),
    .empty(emptyProc18East),
    .dataOut(dataInProc18East));

//FIFO 18 TO 19
fifo fifo_proc18_to_proc19(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc18East),
    .full(fullProc18East),
    .dataIn(dataOutProc18East),
    .rd(rdProc19West),
    .empty(emptyProc19West),
    .dataOut(dataInProc19West));

//FIFO 29 TO 19
fifo fifo_proc29_to_proc19(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc29North),
    .full(fullProc29North),
    .dataIn(dataOutProc29North),
    .rd(rdProc19South),
    .empty(emptyProc19South),
    .dataOut(dataInProc19South));

//FIFO 20 TO 30
fifo fifo_proc20_to_proc30(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc20South),
    .full(fullProc20South),
    .dataIn(dataOutProc20South),
    .rd(rdProc30North),
    .empty(emptyProc30North),
    .dataOut(dataInProc30North));

//FIFO 31 TO 21
fifo fifo_proc31_to_proc21(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc31North),
    .full(fullProc31North),
    .dataIn(dataOutProc31North),
    .rd(rdProc21South),
    .empty(emptyProc21South),
    .dataOut(dataInProc21South));

//FIFO 21 TO 22
fifo fifo_proc21_to_proc22(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc21East),
    .full(fullProc21East),
    .dataIn(dataOutProc21East),
    .rd(rdProc22West),
    .empty(emptyProc22West),
    .dataOut(dataInProc22West));

//FIFO 32 TO 22
fifo fifo_proc32_to_proc22(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc32North),
    .full(fullProc32North),
    .dataIn(dataOutProc32North),
    .rd(rdProc22South),
    .empty(emptyProc22South),
    .dataOut(dataInProc22South));

//FIFO 22 TO 23
fifo fifo_proc22_to_proc23(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc22East),
    .full(fullProc22East),
    .dataIn(dataOutProc22East),
    .rd(rdProc23West),
    .empty(emptyProc23West),
    .dataOut(dataInProc23West));

//FIFO 33 TO 23
fifo fifo_proc33_to_proc23(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc33North),
    .full(fullProc33North),
    .dataIn(dataOutProc33North),
    .rd(rdProc23South),
    .empty(emptyProc23South),
    .dataOut(dataInProc23South));

//FIFO 23 TO 24
fifo fifo_proc23_to_proc24(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc23East),
    .full(fullProc23East),
    .dataIn(dataOutProc23East),
    .rd(rdProc24West),
    .empty(emptyProc24West),
    .dataOut(dataInProc24West));

//FIFO 24 TO 34
fifo fifo_proc24_to_proc34(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc24South),
    .full(fullProc24South),
    .dataIn(dataOutProc24South),
    .rd(rdProc34North),
    .empty(emptyProc34North),
    .dataOut(dataInProc34North));

//FIFO 24 TO 25
fifo fifo_proc24_to_proc25(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc24East),
    .full(fullProc24East),
    .dataIn(dataOutProc24East),
    .rd(rdProc25West),
    .empty(emptyProc25West),
    .dataOut(dataInProc25West));

//FIFO 25 TO 35
fifo fifo_proc25_to_proc35(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc25South),
    .full(fullProc25South),
    .dataIn(dataOutProc25South),
    .rd(rdProc35North),
    .empty(emptyProc35North),
    .dataOut(dataInProc35North));

//FIFO 25 TO 26
fifo fifo_proc25_to_proc26(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc25East),
    .full(fullProc25East),
    .dataIn(dataOutProc25East),
    .rd(rdProc26West),
    .empty(emptyProc26West),
    .dataOut(dataInProc26West));

//FIFO 36 TO 26
fifo fifo_proc36_to_proc26(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc36North),
    .full(fullProc36North),
    .dataIn(dataOutProc36North),
    .rd(rdProc26South),
    .empty(emptyProc26South),
    .dataOut(dataInProc26South));

//FIFO 26 TO 36
fifo fifo_proc26_to_proc36(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc26South),
    .full(fullProc26South),
    .dataIn(dataOutProc26South),
    .rd(rdProc36North),
    .empty(emptyProc36North),
    .dataOut(dataInProc36North));

//FIFO 27 TO 26
fifo fifo_proc27_to_proc26(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc27West),
    .full(fullProc27West),
    .dataIn(dataOutProc27West),
    .rd(rdProc26East),
    .empty(emptyProc26East),
    .dataOut(dataInProc26East));

//FIFO 26 TO 27
fifo fifo_proc26_to_proc27(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc26East),
    .full(fullProc26East),
    .dataIn(dataOutProc26East),
    .rd(rdProc27West),
    .empty(emptyProc27West),
    .dataOut(dataInProc27West));

//FIFO 37 TO 27
fifo fifo_proc37_to_proc27(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc37North),
    .full(fullProc37North),
    .dataIn(dataOutProc37North),
    .rd(rdProc27South),
    .empty(emptyProc27South),
    .dataOut(dataInProc27South));

//FIFO 27 TO 28
fifo fifo_proc27_to_proc28(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc27East),
    .full(fullProc27East),
    .dataIn(dataOutProc27East),
    .rd(rdProc28West),
    .empty(emptyProc28West),
    .dataOut(dataInProc28West));

//FIFO 28 TO 29
fifo fifo_proc28_to_proc29(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc28East),
    .full(fullProc28East),
    .dataIn(dataOutProc28East),
    .rd(rdProc29West),
    .empty(emptyProc29West),
    .dataOut(dataInProc29West));

//FIFO 30 TO 40
fifo fifo_proc30_to_proc40(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc30South),
    .full(fullProc30South),
    .dataIn(dataOutProc30South),
    .rd(rdProc40North),
    .empty(emptyProc40North),
    .dataOut(dataInProc40North));

//FIFO 30 TO 31
fifo fifo_proc30_to_proc31(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc30East),
    .full(fullProc30East),
    .dataIn(dataOutProc30East),
    .rd(rdProc31West),
    .empty(emptyProc31West),
    .dataOut(dataInProc31West));

//FIFO 41 TO 31
fifo fifo_proc41_to_proc31(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc41North),
    .full(fullProc41North),
    .dataIn(dataOutProc41North),
    .rd(rdProc31South),
    .empty(emptyProc31South),
    .dataOut(dataInProc31South));

//FIFO 31 TO 41
fifo fifo_proc31_to_proc41(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc31South),
    .full(fullProc31South),
    .dataIn(dataOutProc31South),
    .rd(rdProc41North),
    .empty(emptyProc41North),
    .dataOut(dataInProc41North));

//FIFO 32 TO 31
fifo fifo_proc32_to_proc31(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc32West),
    .full(fullProc32West),
    .dataIn(dataOutProc32West),
    .rd(rdProc31East),
    .empty(emptyProc31East),
    .dataOut(dataInProc31East));

//FIFO 42 TO 32
fifo fifo_proc42_to_proc32(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc42North),
    .full(fullProc42North),
    .dataIn(dataOutProc42North),
    .rd(rdProc32South),
    .empty(emptyProc32South),
    .dataOut(dataInProc32South));

//FIFO 32 TO 33
fifo fifo_proc32_to_proc33(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc32East),
    .full(fullProc32East),
    .dataIn(dataOutProc32East),
    .rd(rdProc33West),
    .empty(emptyProc33West),
    .dataOut(dataInProc33West));

//FIFO 34 TO 44
fifo fifo_proc34_to_proc44(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc34South),
    .full(fullProc34South),
    .dataIn(dataOutProc34South),
    .rd(rdProc44North),
    .empty(emptyProc44North),
    .dataOut(dataInProc44North));

//FIFO 35 TO 45
fifo fifo_proc35_to_proc45(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc35South),
    .full(fullProc35South),
    .dataIn(dataOutProc35South),
    .rd(rdProc45North),
    .empty(emptyProc45North),
    .dataOut(dataInProc45North));

//FIFO 35 TO 36
fifo fifo_proc35_to_proc36(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc35East),
    .full(fullProc35East),
    .dataIn(dataOutProc35East),
    .rd(rdProc36West),
    .empty(emptyProc36West),
    .dataOut(dataInProc36West));

//FIFO 36 TO 46
fifo fifo_proc36_to_proc46(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc36South),
    .full(fullProc36South),
    .dataIn(dataOutProc36South),
    .rd(rdProc46North),
    .empty(emptyProc46North),
    .dataOut(dataInProc46North));

//FIFO 37 TO 36
fifo fifo_proc37_to_proc36(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc37West),
    .full(fullProc37West),
    .dataIn(dataOutProc37West),
    .rd(rdProc36East),
    .empty(emptyProc36East),
    .dataOut(dataInProc36East));

//FIFO 36 TO 37
fifo fifo_proc36_to_proc37(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc36East),
    .full(fullProc36East),
    .dataIn(dataOutProc36East),
    .rd(rdProc37West),
    .empty(emptyProc37West),
    .dataOut(dataInProc37West));

//FIFO 37 TO 47
fifo fifo_proc37_to_proc47(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc37South),
    .full(fullProc37South),
    .dataIn(dataOutProc37South),
    .rd(rdProc47North),
    .empty(emptyProc47North),
    .dataOut(dataInProc47North));

//FIFO 38 TO 37
fifo fifo_proc38_to_proc37(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc38West),
    .full(fullProc38West),
    .dataIn(dataOutProc38West),
    .rd(rdProc37East),
    .empty(emptyProc37East),
    .dataOut(dataInProc37East));

//FIFO 48 TO 38
fifo fifo_proc48_to_proc38(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc48North),
    .full(fullProc48North),
    .dataIn(dataOutProc48North),
    .rd(rdProc38South),
    .empty(emptyProc38South),
    .dataOut(dataInProc38South));

//FIFO 39 TO 38
fifo fifo_proc39_to_proc38(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc39West),
    .full(fullProc39West),
    .dataIn(dataOutProc39West),
    .rd(rdProc38East),
    .empty(emptyProc38East),
    .dataOut(dataInProc38East));

//FIFO 38 TO 39
fifo fifo_proc38_to_proc39(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc38East),
    .full(fullProc38East),
    .dataIn(dataOutProc38East),
    .rd(rdProc39West),
    .empty(emptyProc39West),
    .dataOut(dataInProc39West));

//FIFO 40 TO 41
fifo fifo_proc40_to_proc41(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc40East),
    .full(fullProc40East),
    .dataIn(dataOutProc40East),
    .rd(rdProc41West),
    .empty(emptyProc41West),
    .dataOut(dataInProc41West));

//FIFO 41 TO 42
fifo fifo_proc41_to_proc42(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc41East),
    .full(fullProc41East),
    .dataIn(dataOutProc41East),
    .rd(rdProc42West),
    .empty(emptyProc42West),
    .dataOut(dataInProc42West));

//FIFO 43 TO 42
fifo fifo_proc43_to_proc42(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc43West),
    .full(fullProc43West),
    .dataIn(dataOutProc43West),
    .rd(rdProc42East),
    .empty(emptyProc42East),
    .dataOut(dataInProc42East));

//FIFO 44 TO 43
fifo fifo_proc44_to_proc43(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc44West),
    .full(fullProc44West),
    .dataIn(dataOutProc44West),
    .rd(rdProc43East),
    .empty(emptyProc43East),
    .dataOut(dataInProc43East));

//FIFO 45 TO 44
fifo fifo_proc45_to_proc44(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc45West),
    .full(fullProc45West),
    .dataIn(dataOutProc45West),
    .rd(rdProc44East),
    .empty(emptyProc44East),
    .dataOut(dataInProc44East));

//FIFO 46 TO 47
fifo fifo_proc46_to_proc47(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc46East),
    .full(fullProc46East),
    .dataIn(dataOutProc46East),
    .rd(rdProc47West),
    .empty(emptyProc47West),
    .dataOut(dataInProc47West));

//FIFO 47 TO 48
fifo fifo_proc47_to_proc48(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc47East),
    .full(fullProc47East),
    .dataIn(dataOutProc47East),
    .rd(rdProc48West),
    .empty(emptyProc48West),
    .dataOut(dataInProc48West));

//FIFO 49 TO 48
fifo fifo_proc49_to_proc48(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc49West),
    .full(fullProc49West),
    .dataIn(dataOutProc49West),
    .rd(rdProc48East),
    .empty(emptyProc48East),
    .dataOut(dataInProc48East));

//FIFO 48 TO 49
fifo fifo_proc48_to_proc49(
    .clk(clk),
    .resetn(resetn),
    .wr(wrProc48East),
    .full(fullProc48East),
    .dataIn(dataOutProc48East),
    .rd(rdProc49West),
    .empty(emptyProc49West),
    .dataOut(dataInProc49West));

    /**************** Boot loader ********************/
    /*******Boot up each processor one by one*********/
    always@(posedge clk)
    begin
    case(processor_select)
        0: begin

            boot_iwe0 = ~resetn;
            boot_dwe0 = ~resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        1: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 = ~resetn;
            boot_dwe1 = ~resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        2: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 = ~resetn;
            boot_dwe2 = ~resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        3: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 = ~resetn;
            boot_dwe3 = ~resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        4: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 = ~resetn;
            boot_dwe4 = ~resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        5: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 = ~resetn;
            boot_dwe5 = ~resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        6: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 = ~resetn;
            boot_dwe6 = ~resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        7: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 = ~resetn;
            boot_dwe7 = ~resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        8: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 = ~resetn;
            boot_dwe8 = ~resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        9: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 = ~resetn;
            boot_dwe9 = ~resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        10: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 = ~resetn;
            boot_dwe10 = ~resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        11: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 = ~resetn;
            boot_dwe11 = ~resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        12: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 = ~resetn;
            boot_dwe12 = ~resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        13: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 = ~resetn;
            boot_dwe13 = ~resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        14: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 = ~resetn;
            boot_dwe14 = ~resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        15: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 = ~resetn;
            boot_dwe15 = ~resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        16: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 = ~resetn;
            boot_dwe16 = ~resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        17: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 = ~resetn;
            boot_dwe17 = ~resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        18: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 = ~resetn;
            boot_dwe18 = ~resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        19: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 = ~resetn;
            boot_dwe19 = ~resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        20: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 = ~resetn;
            boot_dwe20 = ~resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        21: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 = ~resetn;
            boot_dwe21 = ~resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        22: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 = ~resetn;
            boot_dwe22 = ~resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        23: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 = ~resetn;
            boot_dwe23 = ~resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        24: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 = ~resetn;
            boot_dwe24 = ~resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        25: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 = ~resetn;
            boot_dwe25 = ~resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        26: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 = ~resetn;
            boot_dwe26 = ~resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        27: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 = ~resetn;
            boot_dwe27 = ~resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        28: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 = ~resetn;
            boot_dwe28 = ~resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        29: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 = ~resetn;
            boot_dwe29 = ~resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        30: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 = ~resetn;
            boot_dwe30 = ~resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        31: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 = ~resetn;
            boot_dwe31 = ~resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        32: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 = ~resetn;
            boot_dwe32 = ~resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        33: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 = ~resetn;
            boot_dwe33 = ~resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        34: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 = ~resetn;
            boot_dwe34 = ~resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        35: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 = ~resetn;
            boot_dwe35 = ~resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        36: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 = ~resetn;
            boot_dwe36 = ~resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        37: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 = ~resetn;
            boot_dwe37 = ~resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        38: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 = ~resetn;
            boot_dwe38 = ~resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        39: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 = ~resetn;
            boot_dwe39 = ~resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        40: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 = ~resetn;
            boot_dwe40 = ~resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        41: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 = ~resetn;
            boot_dwe41 = ~resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        42: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 = ~resetn;
            boot_dwe42 = ~resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        43: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 = ~resetn;
            boot_dwe43 = ~resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        44: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 = ~resetn;
            boot_dwe44 = ~resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        45: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 = ~resetn;
            boot_dwe45 = ~resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        46: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 = ~resetn;
            boot_dwe46 = ~resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        47: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 = ~resetn;
            boot_dwe47 = ~resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        48: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 = ~resetn;
            boot_dwe48 = ~resetn;
            boot_iwe49 =  resetn;
            boot_dwe49 =  resetn;
        end

        49: begin

            boot_iwe0 =  resetn;
            boot_dwe0 =  resetn;
            boot_iwe1 =  resetn;
            boot_dwe1 =  resetn;
            boot_iwe2 =  resetn;
            boot_dwe2 =  resetn;
            boot_iwe3 =  resetn;
            boot_dwe3 =  resetn;
            boot_iwe4 =  resetn;
            boot_dwe4 =  resetn;
            boot_iwe5 =  resetn;
            boot_dwe5 =  resetn;
            boot_iwe6 =  resetn;
            boot_dwe6 =  resetn;
            boot_iwe7 =  resetn;
            boot_dwe7 =  resetn;
            boot_iwe8 =  resetn;
            boot_dwe8 =  resetn;
            boot_iwe9 =  resetn;
            boot_dwe9 =  resetn;
            boot_iwe10 =  resetn;
            boot_dwe10 =  resetn;
            boot_iwe11 =  resetn;
            boot_dwe11 =  resetn;
            boot_iwe12 =  resetn;
            boot_dwe12 =  resetn;
            boot_iwe13 =  resetn;
            boot_dwe13 =  resetn;
            boot_iwe14 =  resetn;
            boot_dwe14 =  resetn;
            boot_iwe15 =  resetn;
            boot_dwe15 =  resetn;
            boot_iwe16 =  resetn;
            boot_dwe16 =  resetn;
            boot_iwe17 =  resetn;
            boot_dwe17 =  resetn;
            boot_iwe18 =  resetn;
            boot_dwe18 =  resetn;
            boot_iwe19 =  resetn;
            boot_dwe19 =  resetn;
            boot_iwe20 =  resetn;
            boot_dwe20 =  resetn;
            boot_iwe21 =  resetn;
            boot_dwe21 =  resetn;
            boot_iwe22 =  resetn;
            boot_dwe22 =  resetn;
            boot_iwe23 =  resetn;
            boot_dwe23 =  resetn;
            boot_iwe24 =  resetn;
            boot_dwe24 =  resetn;
            boot_iwe25 =  resetn;
            boot_dwe25 =  resetn;
            boot_iwe26 =  resetn;
            boot_dwe26 =  resetn;
            boot_iwe27 =  resetn;
            boot_dwe27 =  resetn;
            boot_iwe28 =  resetn;
            boot_dwe28 =  resetn;
            boot_iwe29 =  resetn;
            boot_dwe29 =  resetn;
            boot_iwe30 =  resetn;
            boot_dwe30 =  resetn;
            boot_iwe31 =  resetn;
            boot_dwe31 =  resetn;
            boot_iwe32 =  resetn;
            boot_dwe32 =  resetn;
            boot_iwe33 =  resetn;
            boot_dwe33 =  resetn;
            boot_iwe34 =  resetn;
            boot_dwe34 =  resetn;
            boot_iwe35 =  resetn;
            boot_dwe35 =  resetn;
            boot_iwe36 =  resetn;
            boot_dwe36 =  resetn;
            boot_iwe37 =  resetn;
            boot_dwe37 =  resetn;
            boot_iwe38 =  resetn;
            boot_dwe38 =  resetn;
            boot_iwe39 =  resetn;
            boot_dwe39 =  resetn;
            boot_iwe40 =  resetn;
            boot_dwe40 =  resetn;
            boot_iwe41 =  resetn;
            boot_dwe41 =  resetn;
            boot_iwe42 =  resetn;
            boot_dwe42 =  resetn;
            boot_iwe43 =  resetn;
            boot_dwe43 =  resetn;
            boot_iwe44 =  resetn;
            boot_dwe44 =  resetn;
            boot_iwe45 =  resetn;
            boot_dwe45 =  resetn;
            boot_iwe46 =  resetn;
            boot_dwe46 =  resetn;
            boot_iwe47 =  resetn;
            boot_dwe47 =  resetn;
            boot_iwe48 =  resetn;
            boot_dwe48 =  resetn;
            boot_iwe49 = ~resetn;
            boot_dwe49 = ~resetn;
        end

        50: begin

            boot_iwe0 = 0;
            boot_dwe0 = 0;
            boot_iwe1 = 0;
            boot_dwe1 = 0;
            boot_iwe2 = 0;
            boot_dwe2 = 0;
            boot_iwe3 = 0;
            boot_dwe3 = 0;
            boot_iwe4 = 0;
            boot_dwe4 = 0;
            boot_iwe5 = 0;
            boot_dwe5 = 0;
            boot_iwe6 = 0;
            boot_dwe6 = 0;
            boot_iwe7 = 0;
            boot_dwe7 = 0;
            boot_iwe8 = 0;
            boot_dwe8 = 0;
            boot_iwe9 = 0;
            boot_dwe9 = 0;
            boot_iwe10 = 0;
            boot_dwe10 = 0;
            boot_iwe11 = 0;
            boot_dwe11 = 0;
            boot_iwe12 = 0;
            boot_dwe12 = 0;
            boot_iwe13 = 0;
            boot_dwe13 = 0;
            boot_iwe14 = 0;
            boot_dwe14 = 0;
            boot_iwe15 = 0;
            boot_dwe15 = 0;
            boot_iwe16 = 0;
            boot_dwe16 = 0;
            boot_iwe17 = 0;
            boot_dwe17 = 0;
            boot_iwe18 = 0;
            boot_dwe18 = 0;
            boot_iwe19 = 0;
            boot_dwe19 = 0;
            boot_iwe20 = 0;
            boot_dwe20 = 0;
            boot_iwe21 = 0;
            boot_dwe21 = 0;
            boot_iwe22 = 0;
            boot_dwe22 = 0;
            boot_iwe23 = 0;
            boot_dwe23 = 0;
            boot_iwe24 = 0;
            boot_dwe24 = 0;
            boot_iwe25 = 0;
            boot_dwe25 = 0;
            boot_iwe26 = 0;
            boot_dwe26 = 0;
            boot_iwe27 = 0;
            boot_dwe27 = 0;
            boot_iwe28 = 0;
            boot_dwe28 = 0;
            boot_iwe29 = 0;
            boot_dwe29 = 0;
            boot_iwe30 = 0;
            boot_dwe30 = 0;
            boot_iwe31 = 0;
            boot_dwe31 = 0;
            boot_iwe32 = 0;
            boot_dwe32 = 0;
            boot_iwe33 = 0;
            boot_dwe33 = 0;
            boot_iwe34 = 0;
            boot_dwe34 = 0;
            boot_iwe35 = 0;
            boot_dwe35 = 0;
            boot_iwe36 = 0;
            boot_dwe36 = 0;
            boot_iwe37 = 0;
            boot_dwe37 = 0;
            boot_iwe38 = 0;
            boot_dwe38 = 0;
            boot_iwe39 = 0;
            boot_dwe39 = 0;
            boot_iwe40 = 0;
            boot_dwe40 = 0;
            boot_iwe41 = 0;
            boot_dwe41 = 0;
            boot_iwe42 = 0;
            boot_dwe42 = 0;
            boot_iwe43 = 0;
            boot_dwe43 = 0;
            boot_iwe44 = 0;
            boot_dwe44 = 0;
            boot_iwe45 = 0;
            boot_dwe45 = 0;
            boot_iwe46 = 0;
            boot_dwe46 = 0;
            boot_iwe47 = 0;
            boot_dwe47 = 0;
            boot_iwe48 = 0;
            boot_dwe48 = 0;
            boot_iwe49 = 0;
            boot_dwe49 = 0;
        end

    endcase
end
endmodule
