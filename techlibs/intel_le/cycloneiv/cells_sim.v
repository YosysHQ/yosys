
module VCC (output V);
   assign V = 1'b1;
endmodule // VCC

module GND (output G);
   assign G = 1'b0;
endmodule // GND

/* Altera Cyclone IV devices Input Buffer Primitive */
module cycloneiv_io_ibuf
  (output o, input i, input ibar);
   assign ibar = ibar;
   assign o    = i;
endmodule // cycloneiv_io_ibuf

/* Altera Cyclone IV devices Output Buffer Primitive */
module cycloneiv_io_obuf
  (output o, input i, input oe);
   assign o  = i;
   assign oe = oe;
endmodule // cycloneiv_io_obuf

/* Altera Cyclone IV LUT Primitive */
module cycloneiv_lcell_comb
  (output combout, cout, 
   input dataa, datab, datac, datad, cin);

   parameter lut_mask      = 16'hFFFF;
   parameter dont_touch    = "off";
   parameter lpm_type      = "cycloneiv_lcell_comb";
   parameter sum_lutc_input = "datac";


endmodule // cycloneiv_lcell_comb


/* Altera D Flip-Flop Primitive */
module dffeas
  (output q,
   input d, clk, clrn, prn, ena,
   input asdata, aload, sclr, sload);

   // Timing simulation is not covered
   parameter power_up="dontcare";
   parameter is_wysiwyg="false";

   reg   q_tmp;
   wire  reset;
   reg [7:0] debug_net;

   assign reset       = (prn && sclr && ~clrn && ena);
   assign q           = q_tmp & 1'b1;

   always @(posedge clk, posedge aload) begin
      if(reset)        q_tmp <= 0;
      else q_tmp <= d;
   end
   assign q = q_tmp;

endmodule // dffeas
