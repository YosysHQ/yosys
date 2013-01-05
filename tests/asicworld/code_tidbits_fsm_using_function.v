//-----------------------------------------------------
// This is FSM demo program using function
// Design Name : fsm_using_function
// File Name   : fsm_using_function.v
//-----------------------------------------------------
module fsm_using_function (
clock      , // clock
reset      , // Active high, syn reset
req_0      , // Request 0
req_1      , // Request 1
gnt_0      , // Grant 0
gnt_1      
);
//-------------Input Ports-----------------------------
input   clock,reset,req_0,req_1;
 //-------------Output Ports----------------------------
output  gnt_0,gnt_1;
//-------------Input ports Data Type-------------------
wire    clock,reset,req_0,req_1;
//-------------Output Ports Data Type------------------
reg     gnt_0,gnt_1;
//-------------Internal Constants--------------------------
parameter SIZE = 3           ;
parameter IDLE  = 3'b001,GNT0 = 3'b010,GNT1 = 3'b100 ;
//-------------Internal Variables---------------------------
reg   [SIZE-1:0]          state        ;// Seq part of the FSM
wire  [SIZE-1:0]          next_state   ;// combo part of FSM
//----------Code startes Here------------------------
assign next_state = fsm_function(state, req_0, req_1);
//----------Function for Combo Logic-----------------
function [SIZE-1:0] fsm_function;
  input  [SIZE-1:0]  state ;	
  input    req_0 ;
  input    req_1 ;
  case(state)
   IDLE : if (req_0 == 1'b1) begin
                fsm_function = GNT0;
              end else if (req_1 == 1'b1) begin
                fsm_function= GNT1;
              end else begin
                fsm_function = IDLE;
              end
   GNT0 : if (req_0 == 1'b1) begin
                fsm_function = GNT0;
              end else begin
                fsm_function = IDLE;
              end
   GNT1 : if (req_1 == 1'b1) begin
                fsm_function = GNT1;
          end else begin
                fsm_function = IDLE;
              end
   default : fsm_function = IDLE;
  endcase
endfunction
//----------Seq Logic-----------------------------
always @ (posedge clock)
begin : FSM_SEQ
  if (reset == 1'b1) begin
    state <= #1 IDLE;
  end else begin
    state <= #1 next_state;
  end
end
//----------Output Logic-----------------------------
always @ (posedge clock)
begin : OUTPUT_LOGIC
if (reset == 1'b1) begin
  gnt_0 <= #1 1'b0;
  gnt_1 <= #1 1'b0;
end
else begin
  case(state)
    IDLE : begin
                  gnt_0 <= #1 1'b0;
                  gnt_1 <= #1 1'b0;
               end
   GNT0 : begin
                   gnt_0 <= #1 1'b1;
                   gnt_1 <= #1 1'b0;
                end
   GNT1 : begin
                   gnt_0 <= #1 1'b0;
                   gnt_1 <= #1 1'b1;
                end
   default : begin
                    gnt_0 <= #1 1'b0;
                    gnt_1 <= #1 1'b0;
                  end
  endcase
end
end // End Of Block OUTPUT_LOGIC

endmodule // End of Module arbiter
