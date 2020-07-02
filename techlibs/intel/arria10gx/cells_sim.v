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



