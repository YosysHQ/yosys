module parallel_scalar(input a, output q);
  assign q = ~a;
  specify
    (a => q) = 1;
  endspecify
endmodule

module parallel_vector(input [3:0] a, output [3:0] q);
  assign q = ~a;
  specify
    (a => q) = (2, 3);
  endspecify
endmodule

module full_vector(input [3:0] a, output [1:0] q);
  assign q = ~a;
  specify
    (a *> q) = (4:5:6, 7:8:9);
  endspecify
endmodule

module selected_terminals(input [7:0] a, output [4:0] q);
  assign q = ~a;
  specify
    (a[6:4] => q[3:1]) = 10;
  endspecify
endmodule

module positive_path(input a, output q);
  assign q = ~a;
  specify
    (a +=> q) = 11;
  endspecify
endmodule

module negative_path(input a, output q);
  assign q = ~a;
  specify
    (a -=> q) = 12;
  endspecify
endmodule

module conditional_path(input a, en, output q);
  assign q = ~a;
  specify
    if (en) (a => q) = 13;
  endspecify
endmodule

module conditional_expression(input a, en, en2, output q);
  assign q = ~a;
  specify
    if (en & en2) (a *> q) = 14;
  endspecify
endmodule

module single_triple(input a, output q);
  assign q = ~a;
  specify
    (a => q) = 7:8:9;
  endspecify
endmodule

module delays_3(input a, output q);
  assign q = ~a;
  specify
    (a => q) = (1, 2, 3);
  endspecify
endmodule

module delays_6(input a, output q);
  assign q = ~a;
  specify
    (a => q) = (1, 2, 3, 4, 5, 6);
  endspecify
endmodule

module delays_12(input a, output q);
  assign q = ~a;
  specify
    (a => q) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
  endspecify
endmodule

module posedge_parallel(input clk, d, output reg q);
  always @(posedge clk) q <= d;
  specify
    (posedge clk => (q : d)) = 15;
  endspecify
endmodule

module negedge_full(input clk, input [2:0] d, output reg [2:0] q);
  always @(negedge clk) q <= d;
  specify
    (negedge clk *> (q +: d)) = (16, 17);
  endspecify
endmodule

module data_negative(input clk, d, output reg q);
  always @(posedge clk) q <= d;
  specify
    (clk => (q -: d)) = 18;
  endspecify
endmodule

module source_and_data_polarity(input clk, d, output reg q);
  always @(posedge clk) q <= d;
  specify
    (posedge clk +*> (q -: d)) = 19;
  endspecify
endmodule

module selected_edge_terminals(input [1:0] clk, input [2:0] d, output reg [1:0] q);
  always @(posedge clk[0]) q <= d[1:0];
  specify
    (posedge clk[0] => (q[1] +: d[2])) = 20;
  endspecify
endmodule

module data_expression(input clk, d, output reg q);
  always @(posedge clk) q <= ~d;
  specify
    (posedge clk *> (q : ~d)) = 21;
  endspecify
endmodule

module conditional_edge(input clk, en, d, output reg q);
  always @(posedge clk) q <= d;
  specify
    if (en) (posedge clk *> (q : d)) = (22:23:24, 25:26:27);
  endspecify
endmodule

module timing_checks(input clk, other_clk, en, en2, rst, input [3:0] d, output q);
  assign q = ^d;
  specify
    $setup(d, posedge clk &&& en, 1:2:3);
    $hold(negedge clk &&& en, d &&& en2, 4);
    $setuphold(posedge clk &&& en, d &&& en2, 5:6:7, 8:9:10);
    $recovery(posedge rst, posedge clk, 11);
    $removal(negedge rst, negedge clk, 12);
    $recrem(posedge rst, posedge clk &&& en, 13, 14);
    $skew(posedge clk, negedge other_clk, 15);
    $timeskew(posedge clk &&& en, negedge other_clk &&& en2, 16);
    $fullskew(posedge clk, negedge other_clk, 17, 18);
    $nochange(posedge clk, d &&& en, -2:-1:0, 1:2:3);
  endspecify
endmodule

(* blackbox *)
module blackbox_timing(input a, en, en2, output q);
  assign q = ~a;
  specify
    if (en & en2) (a => q) = 28;
  endspecify
endmodule

(* whitebox *)
module whitebox_timing(input a, output q);
  assign q = ~a;
  specify
    (a => q) = 29;
  endspecify
endmodule
