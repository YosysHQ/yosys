//-----------------------------------------------------
// Design Name : clk_div_45
// File Name   : clk_div_45.v
// Function    : Divide by 4.5
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module clk_div_45 (
clk_in, // Input Clock
enable, // Enable is sync with falling edge of clk_in
clk_out // Output Clock
);

// --------------Port Declaration-----------------------
input      clk_in     ;
input      enable     ;
output     clk_out    ;

//--------------Port data type declaration-------------
wire       clk_in     ;
wire       enable     ;
wire       clk_out    ;

//--------------Internal Registers----------------------
reg   [3:0] counter1   ;
reg   [3:0] counter2   ;
reg         toggle1    ;
reg         toggle2    ;

//--------------Code Starts Here-----------------------
always @ (posedge clk_in)
if (enable == 1'b0) begin 
   counter1 <= 4'b0;
   toggle1  <= 0;
end else if ((counter1 == 3 && toggle2) || (~toggle1 && counter1 == 4))  begin
   counter1 <= 4'b0;
   toggle1  <= ~toggle1;
end else   begin
   counter1 <= counter1 + 1;
end
   
always @ (negedge clk_in)
if (enable == 1'b0) begin
  counter2 <= 4'b0;
  toggle2  <= 0;
end else if ((counter2 == 3 && ~toggle2) || (toggle2 && counter2 == 4))  begin
  counter2 <= 4'b0;
  toggle2  <= ~toggle2;
end  else   begin
  counter2 <= counter2 + 1;
end

assign  clk_out = (counter1 <3 && counter2 < 3) & enable;

endmodule
