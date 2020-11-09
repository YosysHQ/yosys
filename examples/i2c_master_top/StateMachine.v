// -----------------------------------------------------------------------------
// title          : Sensor Manager Statemachine
// project        : ULP Sensor Hub
// -----------------------------------------------------------------------------
// file           : StateMachine.v
// author         : Glen Gomes
// company        : QuickLogic Corp
// created        : 2013/12/06	
// last update    : 2013/12/06
// platform       : PolarPro III
// standard       : Verilog 2001
// -----------------------------------------------------------------------------
// description: The Sensor Manger Statemachine is responsible for controlling the
//              operations of the Sensor Manager. These include performing
//              transfers between Sensor Memory and various registers.
// -----------------------------------------------------------------------------
// copyright (c) 2013
// -----------------------------------------------------------------------------
// revisions  :
// date            version    author         description
// 2013/12/06      1.0        Glen Gomes     created
// -----------------------------------------------------------------------------
// Comments: This solution is specifically for use with the QuickLogic
//           PolarPro III device. 
// -----------------------------------------------------------------------------

`timescale 1ns/10ps

module StateMachine (

               CLK_IN,
               RESET_IN,

			   RUNTIME_ADDRESS,
               CONTROL_JUMP_REG_DCD,
               SAVE_REG_2_MEM,

               WB_ACK_I,
               WB_BUSY_I,
			   WB_BUSY_POLL_I,

               WB_WE_O,
               WB_STB_O,
               WB_CYC_O,

               SM_CNTL_REG_RUN,
               SM_CNTL_INIT_SEQ,
               SM_READ_DATA,

               SM_INSTR_PTR,
               SM_READ_SELECT,

               SM_WRITE_SELECT,

               SM_BUSY

               );
  

//-----Port Signals--------------------
//

input          CLK_IN;
input          RESET_IN;

input    [7:0] RUNTIME_ADDRESS;
input          CONTROL_JUMP_REG_DCD;
input          SAVE_REG_2_MEM;

input          WB_ACK_I;
input          WB_BUSY_I;
input          WB_BUSY_POLL_I;

output         WB_WE_O;
output         WB_STB_O;
output         WB_CYC_O;

input          SM_CNTL_REG_RUN;
input          SM_CNTL_INIT_SEQ;
input    [7:0] SM_READ_DATA;

output   [7:0] SM_INSTR_PTR;
output         SM_READ_SELECT;

output         SM_WRITE_SELECT;

output         SM_BUSY;


wire           CLK_IN;
wire           RESET_IN;

wire     [7:0] RUNTIME_ADDRESS;
wire           CONTROL_JUMP_REG_DCD;
wire           SAVE_REG_2_MEM;

wire           WB_ACK_I;
wire           WB_BUSY_I;
wire           WB_BUSY_POLL_I;

reg            WB_WE_O;
reg            wb_we_o_nxt;

reg            WB_STB_O;
reg            wb_stb_o_nxt;

reg            WB_CYC_O;
reg            wb_cyc_o_nxt;

wire           SM_CNTL_REG_RUN;
wire           SM_CNTL_INIT_SEQ;
wire     [7:0] SM_READ_DATA;

reg      [7:0] SM_INSTR_PTR;
reg      [7:0] sm_instr_ptr_nxt;

reg            SM_READ_SELECT;
reg            sm_read_select_nxt;

reg            SM_WRITE_SELECT;
reg            sm_write_select_nxt;

reg            SM_BUSY;
reg            sm_busy_nxt;

//-----Internal Signals--------------------
//


//
// Define the Statemachine registers
//
reg      [3:0] sensor_manager_sm;
reg      [3:0] sensor_manager_sm_nxt;


//
// Define the Instruction Pointer variables
//

reg            sm_instr_ptr_ce;
reg            sm_instr_ptr_ce_nxt;

reg            sm_instr_ptr_ld;
reg            sm_instr_ptr_ld_nxt;

reg            sm_instr_ptr_sel;
reg            sm_instr_ptr_sel_nxt;



//------Define Parameters---------
//

//
// Define the Sensor Manager Statemachine States
//
// Note: These states are chosen to allow for overlap of various signals
//       during operation. This overlap should help reduce timing
//       dependancies.
//
parameter SM_IDLE           = 4'h0;
parameter SM_INC_PTR        = 4'h1;
parameter SM_INST_RD        = 4'h2;
//parameter SM_INST_DCD       = 4'h3; // Note: Will be used for TimeStamp Support in a future design
parameter SM_REG_WR         = 4'h4;
parameter SM_REG_RD         = 4'h5;
parameter SM_WAIT_BUSY_ON   = 4'h6;
parameter SM_WAIT_BUSY_OFF  = 4'h7;


//
// Sensor Manager Initialization Start Address
//
// Note: The previous IP used the reset of the "RuntimeAddress" register to
//       select the sensor initialization code. This value explicity selects
//       the value for the start (or re-start) of initialization.
//
parameter SM_INIT_INSTR_ADR = 8'h0; // Address for the start in initialization instructions


//------Logic Operations----------
//

//
// Define the Instruction Pointer
//
// Note: This pointer can start at either the sensor initialization code start
//       address or the run-time code start address. 
//
always @( SM_INSTR_PTR         or
		  sm_instr_ptr_ld      or
		  sm_instr_ptr_ce      or
		  sm_instr_ptr_sel     or
		  SM_READ_DATA         or
          CONTROL_JUMP_REG_DCD or
		  RUNTIME_ADDRESS
		 )
begin
	case({sm_instr_ptr_ld, sm_instr_ptr_ce})
	2'b00: sm_instr_ptr_nxt    <= SM_INSTR_PTR;        // Hold Current Value
	2'b01: sm_instr_ptr_nxt    <= SM_INSTR_PTR + 1'b1; // Increment to the next address
	2'b10:
	begin
        case({CONTROL_JUMP_REG_DCD, sm_instr_ptr_sel})
        2'b00: sm_instr_ptr_nxt <= SM_INIT_INSTR_ADR;  // Initialization Code Address
        2'b01: sm_instr_ptr_nxt <= RUNTIME_ADDRESS;    //       Run-time Code Address
        2'b10: sm_instr_ptr_nxt <= SM_READ_DATA[7:0];  //           Jump      Address
        2'b11: sm_instr_ptr_nxt <= SM_READ_DATA[7:0];  //           Jump      Address
        endcase
	end
	2'b11: sm_instr_ptr_nxt    <= SM_INSTR_PTR;        // Hold Current Value
	endcase
end


// Define the registers associated with the Sensor Manager Statemachine
//
always @(posedge CLK_IN or posedge RESET_IN) 
begin
    if (RESET_IN)
    begin
        sensor_manager_sm  <= SM_IDLE;

        SM_INSTR_PTR       <=  8'h0;
        sm_instr_ptr_ce    <=  1'b0;
        sm_instr_ptr_ld    <=  1'b0;
        sm_instr_ptr_sel   <=  1'b0;

        WB_WE_O            <=  1'b0;
        WB_STB_O           <=  1'b0;
		WB_CYC_O           <=  1'b0;

        SM_READ_SELECT     <=  1'b0;
        SM_WRITE_SELECT    <=  1'b0;

        SM_BUSY            <=  1'b0;
    end
    else 
    begin  
        sensor_manager_sm  <= sensor_manager_sm_nxt;    

        SM_INSTR_PTR       <= sm_instr_ptr_nxt;
        sm_instr_ptr_ce    <= sm_instr_ptr_ce_nxt;
        sm_instr_ptr_ld    <= sm_instr_ptr_ld_nxt;
        sm_instr_ptr_sel   <= sm_instr_ptr_sel_nxt;

        WB_WE_O            <=  wb_we_o_nxt;
        WB_STB_O           <=  wb_stb_o_nxt;
		WB_CYC_O           <=  wb_cyc_o_nxt;

        SM_READ_SELECT     <= sm_read_select_nxt;
        SM_WRITE_SELECT    <= sm_write_select_nxt;

        SM_BUSY            <= sm_busy_nxt;
 	end
end   


// Define the Sensor Manager Statemachine
//
always @( sensor_manager_sm     or
          SM_CNTL_INIT_SEQ      or
          SM_CNTL_REG_RUN       or
          CONTROL_JUMP_REG_DCD  or
          SAVE_REG_2_MEM        or
          WB_BUSY_I             or
		  WB_BUSY_POLL_I        or
		  WB_ACK_I
         )
begin
    case(sensor_manager_sm)
    SM_IDLE:
	begin
		case({SM_CNTL_INIT_SEQ, SM_CNTL_REG_RUN})
		2'b00:    // No Activity
		begin
            sensor_manager_sm_nxt <= SM_IDLE;

		    sm_busy_nxt           <= 1'b0;
            sm_instr_ptr_ld_nxt   <= 1'b0;
            sm_instr_ptr_sel_nxt  <= 1'b0;
        end
		2'b01:    // Start at the Sensor Run-Time Code
		begin
            sensor_manager_sm_nxt <= SM_INC_PTR;

		    sm_busy_nxt           <= 1'b1;
            sm_instr_ptr_ld_nxt   <= 1'b1;
            sm_instr_ptr_sel_nxt  <= 1'b1;
        end
		2'b10:    // No Activity
		begin
            sensor_manager_sm_nxt <= SM_IDLE;

		    sm_busy_nxt           <= 1'b0;
            sm_instr_ptr_ld_nxt   <= 1'b0;
            sm_instr_ptr_sel_nxt  <= 1'b0;
        end
		2'b11:    // Start at the Sensor Initialization Code
		begin
            sensor_manager_sm_nxt <= SM_INC_PTR;

		    sm_busy_nxt           <= 1'b1;
            sm_instr_ptr_ld_nxt   <= 1'b1;
            sm_instr_ptr_sel_nxt  <= 1'b0;
        end
        endcase

        sm_instr_ptr_ce_nxt   <= 1'b0;

        sm_read_select_nxt    <= 1'b0;
        sm_write_select_nxt   <= 1'b0;

		wb_we_o_nxt           <= 1'b0;
		wb_stb_o_nxt          <= 1'b0;
		wb_cyc_o_nxt          <= 1'b0;
	end
    SM_INC_PTR:
	begin
        sensor_manager_sm_nxt <= SM_INST_RD;

		sm_busy_nxt           <= 1'b1;

        sm_instr_ptr_ld_nxt   <= 1'b0;
        sm_instr_ptr_ce_nxt   <= 1'b0;
        sm_instr_ptr_sel_nxt  <= 1'b0;

        sm_read_select_nxt    <= 1'b1;
        sm_write_select_nxt   <= 1'b0;

		wb_we_o_nxt           <= 1'b0;
		wb_stb_o_nxt          <= 1'b0;
		wb_cyc_o_nxt          <= 1'b0;
	end
    SM_INST_RD:
	begin
        sensor_manager_sm_nxt <= SM_REG_WR;

		sm_busy_nxt           <= 1'b1;

        sm_instr_ptr_ld_nxt   <= 1'b0;
        sm_instr_ptr_ce_nxt   <= 1'b0;
        sm_instr_ptr_sel_nxt  <= 1'b0;

        sm_read_select_nxt    <= 1'b0;
        sm_write_select_nxt   <= 1'b0;

		wb_we_o_nxt           <= 1'b1;
		wb_stb_o_nxt          <= 1'b1;
		wb_cyc_o_nxt          <= 1'b1;
	end
    SM_REG_WR:
	begin
        sm_instr_ptr_sel_nxt  <= 1'b0;

        sm_read_select_nxt    <= 1'b0;

		case(SM_CNTL_REG_RUN)
		1'b0:  // A write of "0" to bit "0" of the Command register at address "0" turns off 
			   // the Sensor Manager's Statemachine
		begin
		    sensor_manager_sm_nxt <= SM_IDLE;

		    sm_busy_nxt           <= 1'b0;

            sm_instr_ptr_ld_nxt   <= 1'b0;
            sm_instr_ptr_ce_nxt   <= 1'b0;

            sm_write_select_nxt   <= 1'b0;

		    wb_we_o_nxt           <= 1'b0;
		    wb_stb_o_nxt          <= 1'b0;
		    wb_cyc_o_nxt          <= 1'b0;
		end
		1'b1: // Sensor Manager Statemachine is not stopped; continue processing
		begin
		    sm_busy_nxt           <= 1'b1;

		    case({WB_BUSY_POLL_I, WB_ACK_I})
            2'b00:    // Wait for Wish Bone Acknowledge and no need to wait for transfer complete
	        begin
		    	sensor_manager_sm_nxt <= SM_REG_WR;

                sm_instr_ptr_ld_nxt   <= 1'b0;
                sm_instr_ptr_ce_nxt   <= 1'b0;

                sm_write_select_nxt   <= 1'b0;

		        wb_we_o_nxt           <= 1'b1;
		        wb_stb_o_nxt          <= 1'b1;
		        wb_cyc_o_nxt          <= 1'b1;
		    end
            2'b01:    // Wish Bone Acknowledge Received and no need to wait for transfer complete
	        begin
                case(SAVE_REG_2_MEM)
				1'b0: 
				begin
			        sensor_manager_sm_nxt <= SM_INC_PTR;

                    sm_instr_ptr_ld_nxt   <=  CONTROL_JUMP_REG_DCD;
                    sm_instr_ptr_ce_nxt   <= ~CONTROL_JUMP_REG_DCD;

                    sm_write_select_nxt   <= 1'b0;

		            wb_we_o_nxt           <= 1'b0;
		            wb_stb_o_nxt          <= 1'b0;
		            wb_cyc_o_nxt          <= 1'b0;
				end
				1'b1: 
				begin
			        sensor_manager_sm_nxt <= SM_REG_RD;

                    sm_instr_ptr_ld_nxt   <= 1'b0;
                    sm_instr_ptr_ce_nxt   <= 1'b0;

                    sm_write_select_nxt   <= 1'b1;

		            wb_we_o_nxt           <= 1'b0;
		            wb_stb_o_nxt          <= 1'b1;
		            wb_cyc_o_nxt          <= 1'b1;
				end
		        endcase
		    end
            2'b10:    // Wait for Wish Bone Acknowledge and will need to wait for transfer complete
	        begin
			    sensor_manager_sm_nxt <= SM_REG_WR;

                sm_instr_ptr_ld_nxt   <= 1'b0;
                sm_instr_ptr_ce_nxt   <= 1'b0;

                sm_write_select_nxt   <= 1'b0;

		        wb_we_o_nxt           <= 1'b1;
		        wb_stb_o_nxt          <= 1'b1;
		        wb_cyc_o_nxt          <= 1'b1;
		    end
            2'b11:     // Acknowledge received but need to wait for transfer complete
	        begin
			    sensor_manager_sm_nxt <= SM_WAIT_BUSY_ON;

                sm_instr_ptr_ld_nxt   <= 1'b0;
                sm_instr_ptr_ce_nxt   <= 1'b0;

                sm_write_select_nxt   <= 1'b0;

		        wb_we_o_nxt           <= 1'b0;
		        wb_stb_o_nxt          <= 1'b0;
		        wb_cyc_o_nxt          <= 1'b0;
		    end
            endcase
		end
        endcase
	end
    SM_REG_RD:
	begin
		sm_busy_nxt           <= 1'b1;

        sm_instr_ptr_sel_nxt  <= 1'b0;

        sm_read_select_nxt    <= 1'b0;

		wb_we_o_nxt           <= 1'b0;

		case(WB_ACK_I)
        1'b0:    // Waiting for Wish Bone Acknowledge
		begin
            sensor_manager_sm_nxt <= SM_REG_RD;

            sm_instr_ptr_ld_nxt   <= 1'b0;
            sm_instr_ptr_ce_nxt   <= 1'b0;

            sm_write_select_nxt   <= 1'b1;

		    wb_stb_o_nxt          <= 1'b1;
		    wb_cyc_o_nxt          <= 1'b1;
        end
        1'b1:    // Got Wish Bone Acknowledge
        begin
            sensor_manager_sm_nxt <= SM_INC_PTR;

            sm_instr_ptr_ld_nxt   <=  CONTROL_JUMP_REG_DCD;
            sm_instr_ptr_ce_nxt   <= ~CONTROL_JUMP_REG_DCD;

            sm_write_select_nxt   <= 1'b0;

		    wb_stb_o_nxt          <= 1'b0;
		    wb_cyc_o_nxt          <= 1'b0;
        end
        endcase
	end
    SM_WAIT_BUSY_ON:
	begin
		sm_busy_nxt           <= 1'b1;

        sm_instr_ptr_ld_nxt   <= 1'b0;
        sm_instr_ptr_ce_nxt   <= 1'b0;
        sm_instr_ptr_sel_nxt  <= 1'b0;

        sm_read_select_nxt    <= 1'b0;
        sm_write_select_nxt   <= 1'b0;

		wb_we_o_nxt           <= 1'b0;
		wb_stb_o_nxt          <= 1'b0;
		wb_cyc_o_nxt          <= 1'b0;

        case(WB_BUSY_I)
        1'b0: sensor_manager_sm_nxt <= SM_WAIT_BUSY_ON;    // Wait for Busy from I/F
        1'b1: sensor_manager_sm_nxt <= SM_WAIT_BUSY_OFF;   // Got      Busy from I/F
        endcase
	end
    SM_WAIT_BUSY_OFF:
	begin
		sm_busy_nxt           <= 1'b1;

        sm_instr_ptr_ld_nxt   <= 1'b0;
        sm_instr_ptr_sel_nxt  <= 1'b0;

        sm_read_select_nxt    <= 1'b0;

	    wb_we_o_nxt           <= 1'b0;

        case({SAVE_REG_2_MEM, WB_BUSY_I})
        2'b00:    // Wishbone transfer complete; no need to write anything to Sensor Manager Memory
				  // 
				  // Note: Writes to the command register do not enter this state. 
				  //       Therefore, there is no need to check for the end of processing.
		begin
			sensor_manager_sm_nxt <= SM_INC_PTR;

            sm_instr_ptr_ce_nxt   <= 1'b1;
            sm_write_select_nxt   <= 1'b0;

		    wb_stb_o_nxt          <= 1'b0;
		    wb_cyc_o_nxt          <= 1'b0;
		end
        2'b01:    // Wait for Wishbone transfer to complete
		begin
			sensor_manager_sm_nxt <= SM_WAIT_BUSY_OFF;

            sm_instr_ptr_ce_nxt   <= 1'b0;
            sm_write_select_nxt   <= 1'b0;

		    wb_stb_o_nxt          <= 1'b0;
		    wb_cyc_o_nxt          <= 1'b0;
		end
        2'b10:    // Wishbone transfer complete; Write resulting register value to Sensor Manager Memory
		begin
			sensor_manager_sm_nxt <= SM_REG_RD;

            sm_instr_ptr_ce_nxt   <= 1'b0;
            sm_write_select_nxt   <= 1'b1;

		    wb_stb_o_nxt          <= 1'b1;
		    wb_cyc_o_nxt          <= 1'b1;
		end
        2'b11:    // Wait for Wishbone transfer to complete
		begin
			sensor_manager_sm_nxt <= SM_WAIT_BUSY_OFF;

            sm_instr_ptr_ce_nxt   <= 1'b0;
            sm_write_select_nxt   <= 1'b0;

		    wb_stb_o_nxt          <= 1'b0;
		    wb_cyc_o_nxt          <= 1'b0;
		end
        endcase
	end
	default:
	begin
        sensor_manager_sm_nxt <= SM_IDLE;

		sm_busy_nxt           <= 1'b0;

        sm_instr_ptr_ld_nxt   <= 1'b0;
        sm_instr_ptr_ce_nxt   <= 1'b0;
        sm_instr_ptr_sel_nxt  <= 1'b0;

        sm_read_select_nxt    <= 1'b0;
        sm_write_select_nxt   <= 1'b0;

		wb_we_o_nxt           <= 1'b0;
		wb_stb_o_nxt          <= 1'b0;
		wb_cyc_o_nxt          <= 1'b0;
	end
	endcase
end	

endmodule
