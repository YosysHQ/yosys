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
/* Altera Arria 10 GX devices Input Buffer Primitive */
module twentynm_io_ibuf (output o, input i, input ibar);
   assign ibar = ibar;
   assign o    = i;
endmodule // twentynm_io_ibuf

/* Altera Arria 10 GX  devices Output Buffer Primitive */
module twentynm_io_obuf (output o, input i, input oe);
   assign o  = i;
   assign oe = oe;
endmodule // twentynm_io_obuf

/* Altera Arria 10 GX  LUT Primitive */
module twentynm_lcell_comb (output combout, cout, sumout,
                            input  dataa, datab, datac, datad,
                            input  datae, dataf, datag, cin,
                            input  sharein);

parameter lut_mask      = 64'hFFFFFFFFFFFFFFFF;
parameter dont_touch    = "off";
parameter lpm_type      = "twentynm_lcell_comb";
parameter shared_arith  = "off";
parameter extended_lut  = "off";

// TODO: This is still WIP
initial begin
  $display("Simulation model is still under investigation\n");
end

endmodule // twentynm_lcell_comb

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


