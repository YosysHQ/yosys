//==========================================
// Function : Code Gray counter.
// Coder    : Alex Claros F.
// Date     : 15/May/2005.
//=======================================

module GrayCounter
   #(parameter   COUNTER_WIDTH = 4)
   
    (output reg  [COUNTER_WIDTH-1:0]    GrayCount_out,  //'Gray' code count output.
    
     input wire                         Enable_in,  //Count enable.
     input wire                         Clear_in,   //Count reset.
    
     input wire                         Clk);

    /////////Internal connections & variables///////
    reg    [COUNTER_WIDTH-1:0]         BinaryCount;

    /////////Code///////////////////////
    
    always @ (posedge Clk)
        if (Clear_in) begin
            BinaryCount   <= {COUNTER_WIDTH{1'b 0}} + 1;  //Gray count begins @ '1' with
            GrayCount_out <= {COUNTER_WIDTH{1'b 0}};      // first 'Enable_in'.
        end
        else if (Enable_in) begin
            BinaryCount   <= BinaryCount + 1;
            GrayCount_out <= {BinaryCount[COUNTER_WIDTH-1],
                              BinaryCount[COUNTER_WIDTH-2:0] ^ BinaryCount[COUNTER_WIDTH-1:1]};
        end
    
endmodule
