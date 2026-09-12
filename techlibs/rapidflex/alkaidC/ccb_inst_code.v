///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// File name: define.v
// Descriptions: This file is the opcode for ccb tile instructions
// Author: Yihong
// Date: 2025/8/14
// Revision: 0.0.1
// Revision History:
// V0.0.1 - 2025/8/14 initial release
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//Operations
`define ADD     4'b1000
`define SUB     4'b1001
`define PUSH    4'b1010
`define PULL    4'b1011
`define MOV     4'b1100
`define MOV_T1  4'b1101
`define MOV_T2  4'b1110
`define INTR    4'b1111
`define NA      10'h000

// SRC/DES
`define R0      3'b000
`define R1      3'b001
`define R2      3'b010
`define R3      3'b011
`define C0      3'b100
`define C1      3'b101
`define C2      3'b110