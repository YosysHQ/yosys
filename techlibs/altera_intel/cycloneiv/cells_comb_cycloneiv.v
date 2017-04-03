module VCC (output V);
   assign V = 1'b1;
endmodule // VCC

module GND (output G);
   assign G = 1'b0;
endmodule // GND

/* Altera Cyclone IV (GX) devices Input Buffer Primitive */
module cycloneiv_io_ibuf (output o, input i, input ibar);
   assign ibar = ibar;
   assign o    = i;
endmodule // fiftyfivenm_io_ibuf

/* Altera Cyclone IV (GX)  devices Output Buffer Primitive */
module cycloneiv_io_obuf (output o, input i, input oe);
   assign o  = i;
   assign oe = oe;
endmodule // fiftyfivenm_io_obuf

/* Altera MAX10 4-input non-fracturable LUT Primitive */ 
module cycloneiv_lcell_comb (output combout, cout,
                             input dataa, datab, datac, datad, cin);

/* Internal parameters which define the behaviour
   of the LUT primitive.
   lut_mask define the lut function, can be expressed in 16-digit bin or hex.
   sum_lutc_input define the type of LUT (combinational | arithmetic). 
   dont_touch for retiming || carry options.
   lpm_type for WYSIWYG */  
   
parameter lut_mask = 16'hFFFF;
parameter sum_lutc_input = "datac";
parameter dont_touch = "off";
parameter lpm_type = "fiftyfivenm_lcell_comb";
  
reg [1:0] lut_type;  
reg cout_rt;
reg combout_rt;

wire dataa_w;
wire datab_w;
wire datac_w;
wire datad_w;
wire cin_w;

assign dataa_w = dataa;
assign datab_w = datab;
assign datac_w = datac;
assign datad_w = datad;

function lut_data;
input [15:0] mask;
input dataa;
input datab;
input datac;
input datad;

  begin
    lut_data = datad ? (datac ? (datab ? (dataa ? mask[15] : mask[14]) : (dataa ?  mask[13] : mask[12])) 
                     : (datab ? (dataa ? mask[11] : mask[10]) : (dataa ?  mask[ 9] : mask[ 8])))
                     : (datac ? (datab ? ( dataa ? mask[7] : mask[6]) : (dataa ?  mask[5] : mask[4])) 
                     : (datab ? (dataa ? mask[3] : mask[2]) : ( dataa ? mask[1] : mask[0])));
  end

endfunction

initial begin
    if (sum_lutc_input == "datac") lut_type = 0;
    else 
    if (sum_lutc_input == "cin")   lut_type = 1;
    else                           lut_type = 2;
end

always @(dataa_w or datab_w or datac_w or datad_w or cin_w) begin
    if (lut_type == 0) begin
        combout_rt = lut_data(lut_mask, dataa_w, datab_w, 
                            datac_w, datad_w);
    end
    else if (lut_type == 1) begin
        combout_rt = lut_data(lut_mask, dataa_w, datab_w, 
                            cin_w, datad_w);
    end
    cout_rt = lut_data(lut_mask, dataa_w, datab_w, cin_w, 'b0);
end

assign combout = combout_rt & 1'b1;
assign cout = cout_rt & 1'b1;

endmodule // cycloneiv_lcell_comb

// DFF
module dffeas #(parameter power_up="dontcare", is_wysiwyg="false") ( output q, 
								     input d, 
								     input clk, 
								     input clrn, 
								     input prn, 
								     input ena, 
								     input asdata, 
								     input aload, 
								     input sclr, 
  								     input sload );
  reg q;

  always @(posedge clk)
    q <= d;
   
endmodule



