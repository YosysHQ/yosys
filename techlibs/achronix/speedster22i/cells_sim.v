/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
// > c60k28 (Viacheslav, VT) [at] yandex [dot] com
// > Achronix eFPGA technology sim models. User must first simulate the generated \
// > netlist before going to test it on board/custom chip.
// > Changelog: 1) Removed unused VCC/GND modules
// >            2) Altera comments here (?). Removed.
// >            3) Reusing LUT sim model, removed wrong wires and parameters.

module PADIN (output padout, input padin);
   assign padout = padin;
endmodule

module PADOUT (output padout, input padin, input oe);
   assign padout  = padin;
   assign oe = oe;
endmodule

module LUT4 (output dout,
             input  din0, din1, din2, din3);

parameter [15:0] lut_function = 16'hFFFF;
reg combout_rt;
wire dataa_w;
wire datab_w;
wire datac_w;
wire datad_w;

assign dataa_w = din0;
assign datab_w = din1;
assign datac_w = din2;
assign datad_w = din3;

function lut_data;
input [15:0] mask;
input        dataa, datab, datac, datad;
reg [7:0]   s3;
reg [3:0]   s2;
reg [1:0]   s1;
  begin
       s3 = datad ? mask[15:8] : mask[7:0];
       s2 = datac ?   s3[7:4]  :   s3[3:0];
       s1 = datab ?   s2[3:2]  :   s2[1:0];
       lut_data = dataa ? s1[1] : s1[0];
  end
endfunction

always @(dataa_w or datab_w or datac_w or datad_w) begin
   combout_rt = lut_data(lut_function, dataa_w, datab_w,
                         datac_w, datad_w);
end
assign dout = combout_rt & 1'b1;
endmodule

module DFF (output reg q,
            input  d, ck);
   always @(posedge ck)
     q <= d;

endmodule



