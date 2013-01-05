//====================================================
// This is FSM demo program using single always
// for both seq and combo logic
// Design Name : fsm_using_single_always
// File Name   : fsm_using_single_always.v
//=====================================================
module fsm_using_single_always (
clock      , // clock
reset      , // Active high, syn reset
req_0      , // Request 0
req_1      , // Request 1
gnt_0      , // Grant 0
gnt_1      
);
//=============Input Ports=============================
input   clock,reset,req_0,req_1;
 //=============Output Ports===========================
output  gnt_0,gnt_1;
//=============Input ports Data Type===================
wire    clock,reset,req_0,req_1;
//=============Output Ports Data Type==================
reg     gnt_0,gnt_1;
//=============Internal Constants======================
parameter SIZE = 3           ;
parameter IDLE  = 3'b001,GNT0 = 3'b010,GNT1 = 3'b100 ;
//=============Internal Variables======================
reg   [SIZE-1:0]          state        ;// Seq part of the FSM
reg   [SIZE-1:0]          next_state   ;// combo part of FSM
//==========Code startes Here==========================
always @ (posedge clock)
begin : FSM
if (reset == 1'b1) begin
  state <= #1 IDLE;
  gnt_0 <= 0;
  gnt_1 <= 0;
end else
 case(state)
   IDLE : if (req_0 == 1'b1) begin
                state <= #1 GNT0;
                gnt_0 <= 1;
              end else if (req_1 == 1'b1) begin
                gnt_1 <= 1;
                state <= #1 GNT1;
              end else begin
                state <= #1 IDLE;
              end
   GNT0 : if (req_0 == 1'b1) begin
                state <= #1 GNT0;
              end else begin
                gnt_0 <= 0;
                state <= #1 IDLE;
              end
   GNT1 : if (req_1 == 1'b1) begin
                state <= #1 GNT1;
              end else begin
                gnt_1 <= 0;
                state <= #1 IDLE;
              end
   default : state <= #1 IDLE;
endcase
end

endmodule // End of Module arbiter
