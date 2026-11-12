//-------------------------------------------------
// Block RAM Primitives
//-------------------------------------------------

//-------------------------------------------------
// True Dual-port RAM Core logic
// This module is written in a scalable way
// By default it is configured as 256x36 = 9k-bits
// 
// IMPORTANT: Please do not use this module as a hard ip!!!
module tdpram_core (wclk_i,
                    bwen_ni,
                    wen_ni,
                    waddr_i,
                    data_i,
                    rclk_i,
                    ren_ni,
                    raddr_i,
                    q_o
                   );
// Parameters
parameter ADDR_WIDTH = 8;
parameter DEPTH = 2**ADDR_WIDTH;
parameter BYTE_WIDTH = 9;
parameter NUM_BYTES = 4;
parameter [0:0] IS_WCLK_N = 1'b0; // Indicate if the write clock is triggered at negative edge: 1 = Yes; 0 = No
parameter [0:0] IS_RCLK_N = 1'b0; // Indicate if the read clock is triggered at negative edge: 1 = Yes; 0 = No

input ren_ni;
input wen_ni;
input [0:ADDR_WIDTH-1] raddr_i;
input [0:ADDR_WIDTH-1] waddr_i;
input [0:BYTE_WIDTH*NUM_BYTES-1] bwen_ni;
input [0:BYTE_WIDTH*NUM_BYTES-1] data_i;
input wclk_i;
input rclk_i;
output [0:BYTE_WIDTH*NUM_BYTES-1] q_o;

reg [0:NUM_BYTES*BYTE_WIDTH-1] ram[0:DEPTH-1];
reg [0:NUM_BYTES*BYTE_WIDTH-1] q_reg;

integer i;

assign q_o = q_reg;

// Initial values are all random, to mimic the actual behavoir of a RAM
initial begin
  for (i = 0; i < DEPTH; i = i + 1) begin
    ram[i] = $random;
  end
  q_reg <= $random;
end

case(|IS_WCLK_N)
  1'b0:
    always @(posedge wclk_i) begin
      if (~wen_ni) begin
        for (i = 0; i < NUM_BYTES * BYTE_WIDTH; i = i + 1) begin
          if (~bwen_ni[i]) begin
            ram[waddr_i][i] <= data_i[i];
          end
        end
      end
    end
  1'b1:
    always @(negedge wclk_i) begin
      if (~wen_ni) begin
        for (i = 0; i < NUM_BYTES * BYTE_WIDTH; i = i + 1) begin
          if (~bwen_ni[i]) begin
            ram[waddr_i][i] <= data_i[i];
          end
        end
      end
    end
endcase

case(|IS_RCLK_N)
  1'b0:
    always @(posedge rclk_i) begin
      if (~ren_ni) begin
        q_reg <= ram[raddr_i];
      end
    end
  1'b1:
    always @(negedge rclk_i) begin
      if (~ren_ni) begin
        q_reg <= ram[raddr_i];
      end
    end
endcase

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 256x36
// - read clock is triggered at
//   - [x] positive edge
//   - [ ] negative edge 
// - write clock is triggered at 
//   - [x] positive edge
//   - [ ] negative edge 
module dpram256x36 (wclk_i,
                    bwen_ni,
                    wen_ni,
                    waddr_i,
                    data_i,
                    rclk_i,
                    ren_ni,
                    raddr_i,
                    q_o
                   );

input ren_ni;
input wen_ni;
input [0:7] raddr_i;
input [0:7] waddr_i;
input [0:35] bwen_ni;
input [0:35] data_i;
input wclk_i;
input rclk_i;
output [0:35] q_o;

  tdpram_core #(
    .ADDR_WIDTH(8),
    .BYTE_WIDTH(9),
    .NUM_BYTES(4),
    .IS_WCLK_N(0),
    .IS_RCLK_N(0)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 256x36
// - read clock is triggered at
//   - [x] positive edge
//   - [ ] negative edge 
// - write clock is triggered at 
//   - [ ] positive edge
//   - [x] negative edge 
module dpram256x36_wclkn (wclk_i,
                          bwen_ni,
                          wen_ni,
                          waddr_i,
                          data_i,
                          rclk_i,
                          ren_ni,
                          raddr_i,
                          q_o
                         );

input ren_ni;
input wen_ni;
input [0:7] raddr_i;
input [0:7] waddr_i;
input [0:35] bwen_ni;
input [0:35] data_i;
input wclk_i;
input rclk_i;
output [0:35] q_o;

  tdpram_core #(
    .ADDR_WIDTH(8),
    .BYTE_WIDTH(9),
    .NUM_BYTES(4),
    .IS_WCLK_N(1),
    .IS_RCLK_N(0)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 256x36
// - read clock is triggered at
//   - [ ] positive edge
//   - [x] negative edge 
// - write clock is triggered at 
//   - [x] positive edge
//   - [ ] negative edge 
module dpram256x36_rclkn (wclk_i,
                          bwen_ni,
                          wen_ni,
                          waddr_i,
                          data_i,
                          rclk_i,
                          ren_ni,
                          raddr_i,
                          q_o
                         );

input ren_ni;
input wen_ni;
input [0:7] raddr_i;
input [0:7] waddr_i;
input [0:35] bwen_ni;
input [0:35] data_i;
input wclk_i;
input rclk_i;
output [0:35] q_o;

  tdpram_core #(
    .ADDR_WIDTH(8),
    .BYTE_WIDTH(9),
    .NUM_BYTES(4),
    .IS_WCLK_N(0),
    .IS_RCLK_N(1)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 256x36
// - read clock is triggered at
//   - [ ] positive edge
//   - [x] negative edge 
// - write clock is triggered at 
//   - [ ] positive edge
//   - [x] negative edge 
module dpram256x36_rwclkn (wclk_i,
                           bwen_ni,
                           wen_ni,
                           waddr_i,
                           data_i,
                           rclk_i,
                           ren_ni,
                           raddr_i,
                           q_o
                          );

input ren_ni;
input wen_ni;
input [0:7] raddr_i;
input [0:7] waddr_i;
input [0:35] bwen_ni;
input [0:35] data_i;
input wclk_i;
input rclk_i;
output [0:35] q_o;

  tdpram_core #(
    .ADDR_WIDTH(8),
    .BYTE_WIDTH(9),
    .NUM_BYTES(4),
    .IS_WCLK_N(1),
    .IS_RCLK_N(1)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 512x18
// - read clock is triggered at
//   - [x] positive edge
//   - [ ] negative edge 
// - write clock is triggered at 
//   - [x] positive edge
//   - [ ] negative edge 
module dpram512x18 (wclk_i,
                    bwen_ni,
                    wen_ni,
                    waddr_i,
                    data_i,
                    rclk_i,
                    ren_ni,
                    raddr_i,
                    q_o
                   );

input ren_ni;
input wen_ni;
input [0:8] raddr_i;
input [0:8] waddr_i;
input [0:17] bwen_ni;
input [0:17] data_i;
input wclk_i;
input rclk_i;
output [0:17] q_o;

  tdpram_core #(
    .ADDR_WIDTH(9),
    .BYTE_WIDTH(9),
    .NUM_BYTES(2),
    .IS_WCLK_N(0),
    .IS_RCLK_N(0)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 512x18
// - read clock is triggered at
//   - [x] positive edge
//   - [ ] negative edge 
// - write clock is triggered at 
//   - [ ] positive edge
//   - [x] negative edge 
module dpram512x18_wclkn (wclk_i,
                          bwen_ni,
                          wen_ni,
                          waddr_i,
                          data_i,
                          rclk_i,
                          ren_ni,
                          raddr_i,
                          q_o
                         );

input ren_ni;
input wen_ni;
input [0:8] raddr_i;
input [0:8] waddr_i;
input [0:17] bwen_ni;
input [0:17] data_i;
input wclk_i;
input rclk_i;
output [0:17] q_o;

  tdpram_core #(
    .ADDR_WIDTH(9),
    .BYTE_WIDTH(9),
    .NUM_BYTES(2),
    .IS_WCLK_N(1),
    .IS_RCLK_N(0)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 512x18
// - read clock is triggered at
//   - [ ] positive edge
//   - [x] negative edge 
// - write clock is triggered at 
//   - [x] positive edge
//   - [ ] negative edge 
module dpram512x18_rclkn (wclk_i,
                          bwen_ni,
                          wen_ni,
                          waddr_i,
                          data_i,
                          rclk_i,
                          ren_ni,
                          raddr_i,
                          q_o
                         );

input ren_ni;
input wen_ni;
input [0:8] raddr_i;
input [0:8] waddr_i;
input [0:17] bwen_ni;
input [0:17] data_i;
input wclk_i;
input rclk_i;
output [0:17] q_o;

  tdpram_core #(
    .ADDR_WIDTH(9),
    .BYTE_WIDTH(9),
    .NUM_BYTES(2),
    .IS_WCLK_N(0),
    .IS_RCLK_N(1)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 512x18
// - read clock is triggered at
//   - [ ] positive edge
//   - [x] negative edge 
// - write clock is triggered at 
//   - [ ] positive edge
//   - [x] negative edge 
module dpram512x18_rwclkn (wclk_i,
                           bwen_ni,
                           wen_ni,
                           waddr_i,
                           data_i,
                           rclk_i,
                           ren_ni,
                           raddr_i,
                           q_o
                          );

input ren_ni;
input wen_ni;
input [0:8] raddr_i;
input [0:8] waddr_i;
input [0:17] bwen_ni;
input [0:17] data_i;
input wclk_i;
input rclk_i;
output [0:17] q_o;

  tdpram_core #(
    .ADDR_WIDTH(9),
    .BYTE_WIDTH(9),
    .NUM_BYTES(2),
    .IS_WCLK_N(1),
    .IS_RCLK_N(1)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 1024x9
// - read clock is triggered at
//   - [x] positive edge
//   - [ ] negative edge 
// - write clock is triggered at 
//   - [x] positive edge
//   - [ ] negative edge 
module dpram1024x9 (wclk_i,
                    bwen_ni,
                    wen_ni,
                    waddr_i,
                    data_i,
                    rclk_i,
                    ren_ni,
                    raddr_i,
                    q_o
                   );

input ren_ni;
input wen_ni;
input [0:9] raddr_i;
input [0:9] waddr_i;
input [0:8] bwen_ni;
input [0:8] data_i;
input wclk_i;
input rclk_i;
output [0:8] q_o;

  tdpram_core #(
    .ADDR_WIDTH(10),
    .BYTE_WIDTH(9),
    .NUM_BYTES(1),
    .IS_WCLK_N(0),
    .IS_RCLK_N(0)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 1024x9
// - read clock is triggered at
//   - [x] positive edge
//   - [ ] negative edge 
// - write clock is triggered at 
//   - [ ] positive edge
//   - [x] negative edge 
module dpram1024x9_wclkn (wclk_i,
                          bwen_ni,
                          wen_ni,
                          waddr_i,
                          data_i,
                          rclk_i,
                          ren_ni,
                          raddr_i,
                          q_o
                         );

input ren_ni;
input wen_ni;
input [0:9] raddr_i;
input [0:9] waddr_i;
input [0:8] bwen_ni;
input [0:8] data_i;
input wclk_i;
input rclk_i;
output [0:8] q_o;

  tdpram_core #(
    .ADDR_WIDTH(10),
    .BYTE_WIDTH(9),
    .NUM_BYTES(1),
    .IS_WCLK_N(1),
    .IS_RCLK_N(0)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 1024x9
// - read clock is triggered at
//   - [ ] positive edge
//   - [x] negative edge 
// - write clock is triggered at 
//   - [x] positive edge
//   - [ ] negative edge 
module dpram1024x9_rclkn (wclk_i,
                          bwen_ni,
                          wen_ni,
                          waddr_i,
                          data_i,
                          rclk_i,
                          ren_ni,
                          raddr_i,
                          q_o
                         );

input ren_ni;
input wen_ni;
input [0:9] raddr_i;
input [0:9] waddr_i;
input [0:8] bwen_ni;
input [0:8] data_i;
input wclk_i;
input rclk_i;
output [0:8] q_o;

  tdpram_core #(
    .ADDR_WIDTH(10),
    .BYTE_WIDTH(9),
    .NUM_BYTES(1),
    .IS_WCLK_N(0),
    .IS_RCLK_N(1)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 1024x9
// - read clock is triggered at
//   - [ ] positive edge
//   - [x] negative edge 
// - write clock is triggered at 
//   - [ ] positive edge
//   - [x] negative edge 
module dpram1024x9_rwclkn (wclk_i,
                           bwen_ni,
                           wen_ni,
                           waddr_i,
                           data_i,
                           rclk_i,
                           ren_ni,
                           raddr_i,
                           q_o
                          );

input ren_ni;
input wen_ni;
input [0:9] raddr_i;
input [0:9] waddr_i;
input [0:8] bwen_ni;
input [0:8] data_i;
input wclk_i;
input rclk_i;
output [0:8] q_o;

  tdpram_core #(
    .ADDR_WIDTH(10),
    .BYTE_WIDTH(9),
    .NUM_BYTES(1),
    .IS_WCLK_N(1),
    .IS_RCLK_N(1)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 2048x4
// - read clock is triggered at
//   - [x] positive edge
//   - [ ] negative edge 
// - write clock is triggered at 
//   - [x] positive edge
//   - [ ] negative edge 
module dpram2048x4 (wclk_i,
                    bwen_ni,
                    wen_ni,
                    waddr_i,
                    data_i,
                    rclk_i,
                    ren_ni,
                    raddr_i,
                    q_o
                   );

input ren_ni;
input wen_ni;
input [0:10] raddr_i;
input [0:10] waddr_i;
input [0:3] bwen_ni;
input [0:3] data_i;
input wclk_i;
input rclk_i;
output [0:3] q_o;

  tdpram_core #(
    .ADDR_WIDTH(11),
    .BYTE_WIDTH(4),
    .NUM_BYTES(1),
    .IS_WCLK_N(0),
    .IS_RCLK_N(0)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 2048x4
// - read clock is triggered at
//   - [x] positive edge
//   - [ ] negative edge 
// - write clock is triggered at 
//   - [ ] positive edge
//   - [x] negative edge 
module dpram2048x4_wclkn (wclk_i,
                          bwen_ni,
                          wen_ni,
                          waddr_i,
                          data_i,
                          rclk_i,
                          ren_ni,
                          raddr_i,
                          q_o
                         );

input ren_ni;
input wen_ni;
input [0:10] raddr_i;
input [0:10] waddr_i;
input [0:3] bwen_ni;
input [0:3] data_i;
input wclk_i;
input rclk_i;
output [0:3] q_o;

  tdpram_core #(
    .ADDR_WIDTH(11),
    .BYTE_WIDTH(4),
    .NUM_BYTES(1),
    .IS_WCLK_N(1),
    .IS_RCLK_N(0)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 2048x4
// - read clock is triggered at
//   - [ ] positive edge
//   - [x] negative edge 
// - write clock is triggered at 
//   - [x] positive edge
//   - [ ] negative edge 
module dpram2048x4_rclkn (wclk_i,
                          bwen_ni,
                          wen_ni,
                          waddr_i,
                          data_i,
                          rclk_i,
                          ren_ni,
                          raddr_i,
                          q_o
                         );

input ren_ni;
input wen_ni;
input [0:10] raddr_i;
input [0:10] waddr_i;
input [0:3] bwen_ni;
input [0:3] data_i;
input wclk_i;
input rclk_i;
output [0:3] q_o;

  tdpram_core #(
    .ADDR_WIDTH(11),
    .BYTE_WIDTH(4),
    .NUM_BYTES(1),
    .IS_WCLK_N(0),
    .IS_RCLK_N(1)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule

//-------------------------------------------------
// True Dual-port RAM Core logic 2048x4
// - read clock is triggered at
//   - [ ] positive edge
//   - [x] negative edge 
// - write clock is triggered at 
//   - [ ] positive edge
//   - [x] negative edge 
module dpram2048x4_rwclkn (wclk_i,
                           bwen_ni,
                           wen_ni,
                           waddr_i,
                           data_i,
                           rclk_i,
                           ren_ni,
                           raddr_i,
                           q_o
                          );

input ren_ni;
input wen_ni;
input [0:10] raddr_i;
input [0:10] waddr_i;
input [0:3] bwen_ni;
input [0:3] data_i;
input wclk_i;
input rclk_i;
output [0:3] q_o;

  tdpram_core #(
    .ADDR_WIDTH(11),
    .BYTE_WIDTH(4),
    .NUM_BYTES(1),
    .IS_WCLK_N(1),
    .IS_RCLK_N(1)
  ) tdpram_core (
    .rclk_i     (rclk_i),
    .wclk_i     (wclk_i),
    .bwen_ni    (bwen_ni),
    .wen_ni     (wen_ni),
    .waddr_i    (waddr_i),
    .data_i     (data_i),
    .ren_ni     (ren_ni),
    .raddr_i    (raddr_i),
    .q_o        (q_o) 
   );

endmodule
