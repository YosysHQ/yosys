// Asymetric RAM - TDP  
// READ_FIRST MODE.
// asym_ram_tdp_read_first.v


module asym_ram_tdp_read_first (clkA, clkB, enaA, weA, enaB, weB, addrA, addrB, diA, doA, diB, doB);
parameter WIDTHB = 4;
parameter SIZEB = 1024;
parameter ADDRWIDTHB = 10;
parameter WIDTHA = 16;
parameter SIZEA = 256;
parameter ADDRWIDTHA = 8;
input clkA;
input clkB;
input weA, weB;
input enaA, enaB;

input [ADDRWIDTHA-1:0] addrA;
input [ADDRWIDTHB-1:0] addrB;
input [WIDTHA-1:0] diA;
input [WIDTHB-1:0] diB;

output [WIDTHA-1:0] doA;
output [WIDTHB-1:0] doB;

`define max(a,b) {(a) > (b) ? (a) : (b)}
`define min(a,b) {(a) < (b) ? (a) : (b)}

function integer log2;
input integer value;
reg [31:0] shifted;
integer res;
begin
 if (value < 2)
  log2 = value;
 else
 begin
  shifted = value-1;
  for (res=0; shifted>0; res=res+1)
   shifted = shifted>>1;
  log2 = res;
 end
end
endfunction

localparam maxSIZE = `max(SIZEA, SIZEB);
localparam maxWIDTH = `max(WIDTHA, WIDTHB);
localparam minWIDTH = `min(WIDTHA, WIDTHB);

localparam RATIO = maxWIDTH / minWIDTH;
localparam log2RATIO = log2(RATIO);

reg [minWIDTH-1:0] RAM [0:maxSIZE-1];
reg [WIDTHA-1:0] readA;
reg [WIDTHB-1:0] readB;

always @(posedge clkB)
begin
 if (enaB) begin
  readB <= RAM[addrB] ;
  if (weB)
   RAM[addrB] <= diB;
 end  
end


always @(posedge clkA)
begin : portA
 integer i;
 reg [log2RATIO-1:0] lsbaddr ;
  for (i=0; i< RATIO; i= i+ 1) begin 
   lsbaddr = i;
  if (enaA) begin
   readA[(i+1)*minWIDTH -1 -: minWIDTH] <= RAM[{addrA, lsbaddr}];

   if (weA)
    RAM[{addrA, lsbaddr}] <= diA[(i+1)*minWIDTH-1 -: minWIDTH];
  end
 end
end

assign doA = readA;
assign doB = readB;

endmodule
