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
/* Altera Cyclone 10 LP devices Input Buffer Primitive */
module cyclone10lp_io_ibuf
  (output o, input i, input ibar);
   assign ibar = ibar;
   assign o    = i;
endmodule // cyclone10lp_io_ibuf

/* Altera Cyclone 10 LP devices Output Buffer Primitive */
module cyclone10lp_io_obuf
  (output o, input i, input oe);
   assign o  = i;
   assign oe = oe;
endmodule // cyclone10lp_io_obuf

/* Altera Cyclone IV (E) 4-input non-fracturable LUT Primitive */
module cyclone10lp_lcell_comb
  (output combout, cout,
   input dataa, datab, datac, datad, cin);

   /* Internal parameters which define the behaviour
    of the LUT primitive.
    lut_mask define the lut function, can be expressed in 16-digit bin or hex.
    sum_lutc_input define the type of LUT (combinational | arithmetic).
    dont_touch for retiming || carry options.
    lpm_type for WYSIWYG */

   parameter lut_mask   = 16'hFFFF;
   parameter dont_touch = "off";
   parameter lpm_type   = "cyclone10lp_lcell_comb";
   parameter sum_lutc_input = "datac";

   reg [1:0]                        lut_type;
   reg                              cout_rt;
   reg                              combout_rt;
   wire                             dataa_w;
   wire                             datab_w;
   wire                             datac_w;
   wire                             datad_w;
   wire                             cin_w;

   assign dataa_w = dataa;
   assign datab_w = datab;
   assign datac_w = datac;
   assign datad_w = datad;

   function lut_data;
      input [15:0]                  mask;
      input                         dataa, datab, datac, datad;
      reg [7:0]                     s3;
      reg [3:0]                     s2;
      reg [1:0]                     s1;
      begin
         s3 = datad ? mask[15:8] : mask[7:0];
         s2 = datac ?   s3[7:4]  :   s3[3:0];
         s1 = datab ?   s2[3:2]  :   s2[1:0];
         lut_data = dataa ? s1[1] : s1[0];
      end

   endfunction

   initial begin
      if (sum_lutc_input == "datac") lut_type = 0;
      else
        if (sum_lutc_input == "cin")   lut_type = 1;
        else begin
           $error("Error in sum_lutc_input. Parameter %s is not a valid value.\n", sum_lutc_input);
           $finish();
        end
   end

   always @(dataa_w or datab_w or datac_w or datad_w or cin_w) begin
      if (lut_type == 0) begin // logic function
         combout_rt = lut_data(lut_mask, dataa_w, datab_w,
                               datac_w, datad_w);
      end
      else if (lut_type == 1) begin // arithmetic function
         combout_rt = lut_data(lut_mask, dataa_w, datab_w,
                               cin_w, datad_w);
      end
      cout_rt = lut_data(lut_mask, dataa_w, datab_w, cin_w, 'b0);
   end

   assign combout = combout_rt & 1'b1;
   assign cout = cout_rt & 1'b1;

endmodule // cyclone10lp_lcell_comb

/* The `dffeas` Intel primitive is a general purpose wrapper
 * for various types of flip-flops. It's a Quartus LPM, and
 * documentation and simulation models are implemented with
 * User Defined Primitives (UDP).
 * This model is suitable for Equivalence Checking and 
 * simulation. 
 * TODO: Add devpor and devclrn behavior. */
module dffeas
  (input wire clk, ena, prn, clrn,
   input wire asdata, aload, sload,
   input wire sclr, d,
   output wire q);

   parameter power_up = "DONT_CARE";
   parameter is_wysiwyg = "false";
   
   wire powerup_value;
   wire async_load;
   wire async_load_zero;
   wire d_next, aset_next, arst_next;
   
   assign powerup_value   = (power_up == "high") ? 1'b1 : 1'b0;
   assign async_load      = (clrn & aload & asdata);
   assign async_load_zero = (clrn & aload & ~asdata);
   assign d_next          = ((sclr) ? 1'b0 : (sload) ? asdata : d);
   assign aset_next       = ((~prn | async_load) ? 1'b1 : 1'b0);
   assign arst_next       = ((~clrn | async_load_zero) ? 1'b1 : 1'b0);
`ifdef SIM
   initial q = powerup_value;
`endif
   dff_prim dffsre (.ck(clk), .en(ena), .d(d_next), .s(aset_next), .r(arst_next), .q(q));
   
endmodule // dffeas

module dff_prim
  (input wire ck, en, d, s, r,
   output reg q);

   wire       d_present;
   wire       d_next;
   wire       past_q;
   
   assign d_present = (en & d);
   assign past_q    = (~en & q);
   assign d_next    = (d_present | past_q);
   
   always @(posedge ck, posedge s, posedge r) begin
      if (r)
	q <= 1'b0;
      else if (s)
	q <= 1'b1;
      else
	q <= d_next;
   end
endmodule // dff_prim
