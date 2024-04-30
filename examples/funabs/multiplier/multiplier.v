`timescale 1ns / 1ps
// fpga4student.com FPGA projects, Verilog projects, VHDL projects
// multiplier 4x4 using Shift/Add Algorithm and 2-phase clocking system
// Verilog project: Verilog code for multiplier

function [8:0] concat54;
    input [4:0] a;
    input [3:0] b;
    begin
        concat54 = {a,b};
    end
endfunction

function [4:0] concat14;
    input [0:0] a;
    input [3:0] b;
    begin
        concat14 = {a,b};
    end
endfunction

function [3:0] high54;
    input [8:0] a;
    begin
        high54 = a[7:4];
    end
endfunction

function [3:0] low54;
    input [8:0] a;
    begin
        low54 = a[3:0];
    end
endfunction

function lowbit;
    input [8:0] a;
    begin
        lowbit = a[0];
    end
endfunction

function high9;
    input [8:0] a;
    begin
        high9 = a[8:8];
    end
endfunction

function [7:0] low18;
    input [8:0] a;
    begin
        low18 = a[7:0];
    end
endfunction

function [4:0] add54;
    input [4:0] a;
    input [3:0] b;
    begin
        add54 = a+b;
    end
endfunction

function [8:0] shiftright9;
    input [8:0] a;
    begin
        shiftright9 = {1'b0,a[8:1]};
    end
endfunction

function [8:0] accumulate;
   input [8:0] acc;
   input [3:0] b;
   begin
      accumulate = {1'b0,acc[7:4],acc[3:0]} + b;
   end
endfunction

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
assign O = low18(ACC); 

initial assume (State==12);

// FSM
always @(posedge clk) begin
    if(reset) begin
        State <= 0;
        ACC <= 0;
    end else begin
        //if((Phi0==1'b1) || (Phi1==1'b1)) begin // 2 phase clocking
        if (State==0) begin
            ACC <= concat54(5'b00000,A); // begin cycle
            Asave <= A;
            Bsave <= B;
            State <= 1;
        end else if(State==1 || State == 3 || State ==5 || State ==7) begin
            if (ACC[0] == 1'b1) begin // add multiplicand
                ACC <= concat54(add54(concat14(1'b0,high54(ACC)),Bsave),low54(ACC));
                State <= State + 1;
            end else begin
                ACC <= shiftright9(ACC);// shift right
                State <= State + 2;
            end
        end else if(State==2 || State == 4 || State ==6 || State ==8) begin
                // shift State
            ACC <= shiftright9(ACC);// shift right
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

