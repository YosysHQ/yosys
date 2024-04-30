`timescale 1ns / 1ps
// fpga4student.com FPGA projects, Verilog projects, VHDL projects
// multiplier 4x4 using Shift/Add Algorithm and 2-phase clocking system
// Verilog project: Verilog code for multiplier

module mult_4x4(
         input clk,reset,start, 
         input[3:0] A,B, 
         output [7:0] O, output Finish
             );
reg [7:0] O;
wire Finish;  
wire Phi0,Phi1;// 2 phase clocking
wire m1,m2,m3,m4;

// state machine
reg[3:0] State;

// Accumulator
reg [8:0] ACC; // Accumulator

reg [3:0] Asave;
reg [3:0] Bsave;

// logic to create 2 phase clocking when starting
//nand u0(m1,start,m2);
//buf #20 u1(m2,m1);
//buf #10 u2(Phi0,m1);// First phase clocking
//not #2 u5(m4,Phi0);
//assign m3=~m1; 
//and #2 u4(Phi1,m3,m4);// Second phase clocking

assign Finish = (State==9)? 1'b1:1'b0; // Finish Flag
assign O = ACC[7:0];

initial assume (State==12);

// FSM
always @(posedge clk) begin
    if(reset) begin
        State <= 0; 
        ACC <= 0; 
    end else begin 
        //if((Phi0==1'b1) || (Phi1==1'b1)) begin // 2 phase clocking
        if (State==0) begin
            ACC[8:4] <= 5'b00000; // begin cycle
            ACC[3:0] <= A; // Load A
            Asave <= A;
            Bsave <= B;
            State <= 1;
        end else if(State==1 || State == 3 || State ==5 || State ==7) begin
                // add/shift State
            if (ACC[0] == 1'b1) begin // add multiplicand
                ACC[8:4] <= {1'b0,ACC[7:4]} + Bsave; 
                State <= State + 1;
            end else begin
                ACC <= {1'b0,ACC[8:1]};// shift right
                State <= State + 2;
            end
        end else if(State==2 || State == 4 || State ==6 || State ==8) begin 
                // shift State
            ACC <= {1'b0,ACC[8:1]}; // shift right
            State <= State + 1;
        end else if(State == 9) begin
            State <= 0;
        end else begin
            State <= 10;
        end
    end
    mult_correct: assert (~Finish || (O==Asave*Bsave));
end 

endmodule
// TestBench
// fpga4student.com FPGA projects, Verilog projects, VHDL projects
// Verilog project: Verilog code for multiplier

module test();
// signals
reg start,reset;
reg[3:0] A,B;
// Outputs
wire [7:0] O;
wire Finish;
wire clk;

// Clock generator
always
begin
    #5 clk = 1;
    #5 clk = 0;
end

// device under test
mult_4x4 dut(clk,reset,start, A,B,O,Finish);
initial begin
reset=1; // reset
#40 start = 0;A =14; B= 11;
#400 reset = 0; 
#40 start = 1; // start
//@(posedge Finish);
//start = 0;
//$finish;
end 

endmodule

