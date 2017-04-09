module graphtest (A,B,X,Y,Z);

input      [3:0] A;
input      [3:0] B;
output reg [3:0] X;
output     [9:0] Y;
output     [7:0] Z;

wire [4:0] t;

assign t[4] = 1'b0;                      // Constant connects to wire
assign t[2:0] = A[2:0] & { 2'b10, B[3]}; // Concatenation of intermediate wire
assign t[3] = A[2] ^ B[3];               // Bitwise-XOR

// assign Y[2:0] = 3'b111;
// assign Y[6:3] = A;
// assign Y[9:7] = t[0:2];
assign Y = {3'b111, A, t[2:0]};          // Direct assignment of concatenation

assign Z[0] = 1'b0;                      // Constant connects to PO
assign Z[1] = t[3];                      // Intermediate sig connects to PO
assign Z[3:2] = A[2:1];                  // PI connects to PO
assign Z[7:4] = {1'b0, B[2:0]};          // Concat of CV and PI connect to PO

always @* begin
  if (A == 4'b1111) begin                // All-Const at port (eq)
    X = B;
  end
  else begin
    X = 4'b0000;                         // All-Const at port (mux)
  end
end

endmodule
