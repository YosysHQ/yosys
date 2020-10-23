/* 
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */
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

   reg cout_tmp;
   reg combout_tmp;

   reg [1:0] isum_lutc_input;
   
   wire dataa_in;
   wire datab_in;
   wire datac_in;
   wire datad_in;
   wire cin_in;

   // Simulation model of 4-input LUT
   function lut4;
      input [15:0] mask;
      input        dataa, datab, datac, datad;
      reg [7:0]    s3;
      reg [3:0]    s2;
      reg [1:0]    s1;
      begin
         s3   = datad ? mask[15:8] : mask[7:0];
         s2   = datac ?   s3[7:4]  :   s3[3:0];
         s1   = datab ?   s2[3:2]  :   s2[1:0];
         lut4 = dataa ? s1[1] : s1[0];
      end
   endfunction // lut4


   initial
   begin
   	if (sum_lutc_input == "datac") 
   		isum_lutc_input = 0;
   	else if (sum_lutc_input == "cin") 
   		isum_lutc_input = 1;
   	else
   	begin
   		$display ("Error: Invalid sum_lutc_input specified\n");
   		$display ("Time: %0t  Instance: %m", $time);
   		isum_lutc_input = 2;
   	end

   end

   always @(datad_in or datac_in or datab_in or dataa_in or cin_in)
   begin
	
   	if (isum_lutc_input == 0) // datac 
   	begin
   		combout_tmp = lut4(lut_mask, dataa_in, datab_in, 
   				datac_in, datad_in);
   	end
   	else if (isum_lutc_input == 1) // cin
   	begin
   		combout_tmp = lut4(lut_mask, dataa_in, datab_in, 
   				cin_in, datad_in);
   	end

   	cout_tmp = lut4(lut_mask, dataa_in, datab_in, cin_in, 'b0);
   end

   and (combout, combout_tmp, 1'b1) ;
   and (cout, cout_tmp, 1'b1) ;
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
