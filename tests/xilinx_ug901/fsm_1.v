// State Machine with single sequential block
//fsm_1.v
module fsm_1(clk,reset,flag,sm_out);
input clk,reset,flag;
output reg sm_out;

parameter s1 = 3'b000;
parameter s2 = 3'b001;
parameter s3 = 3'b010;
parameter s4 = 3'b011;
parameter s5 = 3'b111;

reg [2:0] state;

always@(posedge clk)
  begin
    if(reset)
      begin
        state <= s1;
        sm_out  <= 1'b1;
      end
  else
    begin
     case(state)
       s1: if(flag) 
            begin 
              state <= s2; 
              sm_out <= 1'b1; 
            end
           else
            begin
              state <= s3;
              sm_out <= 1'b0;
            end
       s2: begin state <= s4; sm_out <= 1'b0; end
       s3: begin state <= s4; sm_out <= 1'b0; end
       s4: begin state <= s5; sm_out <= 1'b1; end
       s5: begin state <= s1; sm_out <= 1'b1; end
     endcase
    end
 end
endmodule
