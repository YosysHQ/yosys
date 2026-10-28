// exhaustive switches: the most common arm value replaces Sx as the default

module dominant_explicit(input [1:0] s, output reg [2:0] y, output reg [1:0] z);
  always @* begin
    y = 3'b001;
    z = 2'b00;
    case (s)
      2'b00: begin y = 3'b110; z = 2'b11; end
      2'b01: begin y = 3'b001; z = 2'b00; end
      2'b10: begin y = 3'b001; z = 2'b00; end
      2'b11: begin y = 3'b001; z = 2'b00; end
    endcase
  end
endmodule

module dominant_wire(input [1:0] s, input [2:0] a, output reg [2:0] y);
  always @* begin
    y = a;
    case (s)
      2'b00: y = 3'b110;
      2'b01: y = a;
      2'b10: y = a;
      2'b11: y = a;
    endcase
  end
endmodule

module no_dominant(input [1:0] s, input [2:0] a, b, c, d, output reg [2:0] y);
  always @* begin
    case (s)
      2'b00: y = a;
      2'b01: y = b;
      2'b10: y = c;
      2'b11: y = d;
    endcase
  end
endmodule

// most common value used by less than half of the arms
module plurality(input [2:0] s, input [2:0] a, output reg [2:0] y);
  always @* begin
    case (s)
      3'b000: y = a;
      3'b001: y = a;
      3'b010: y = a;
      3'b011: y = 3'd1;
      3'b100: y = 3'd2;
      3'b101: y = 3'd3;
      3'b110: y = 3'd4;
      3'b111: y = 3'd5;
    endcase
  end
endmodule
