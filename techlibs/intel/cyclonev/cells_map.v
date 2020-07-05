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
// > c60k28 (Viacheslav, VT) [at] yandex [dot] com
// > Intel FPGA technology mapping. User must first simulate the generated \
// > netlist before going to test it on board.

// Input buffer map
module \$__inpad (input I, output O);
   cyclonev_io_ibuf _TECHMAP_REPLACE_ (.o(O), .i(I), .ibar(1'b0));
endmodule

// Output buffer map
module \$__outpad (input I, output O);
   cyclonev_io_obuf _TECHMAP_REPLACE_ (.o(O), .i(I), .oe(1'b1));
endmodule

// LUT Map
module \$lut (A, Y);
   parameter WIDTH  = 0;
   parameter LUT    = 0;
   (* force_downto *)
   input [WIDTH-1:0] A;
   output            Y;
   wire              VCC;
   wire              GND;
   assign {VCC,GND} = {1'b1,1'b0};

   generate
      if (WIDTH == 1) begin
	 assign Y = ~A[0]; // Not need to spend 1 logic cell for such an easy function
      end
      else
        if (WIDTH == 2) begin
           cyclonev_lcell_comb #(.lut_mask({16{LUT}}), .shared_arith("off"), .extended_lut("off"))
           _TECHMAP_REPLACE_
             (.combout(Y),
              .dataa(A[0]),
              .datab(A[1]),
              .datac(VCC),
              .datad(VCC),
              .datae(VCC),
              .dataf(VCC),
              .datag(VCC));
        end
        else
          if(WIDTH == 3) begin
	     cyclonev_lcell_comb #(.lut_mask({8{LUT}}), .shared_arith("off"), .extended_lut("off"))
             _TECHMAP_REPLACE_
               (.combout(Y),
                .dataa(A[0]),
                .datab(A[1]),
                .datac(A[2]),
                .datad(VCC),
                .datae(VCC),
                .dataf(VCC),
                .datag(VCC));
          end
          else
            if(WIDTH == 4) begin
	       cyclonev_lcell_comb #(.lut_mask({4{LUT}}), .shared_arith("off"), .extended_lut("off"))
               _TECHMAP_REPLACE_
                 (.combout(Y),
                  .dataa(A[0]),
                  .datab(A[1]),
                  .datac(A[2]),
                  .datad(A[3]),
                  .datae(VCC),
                  .dataf(VCC),
                  .datag(VCC));
            end
            else
              if(WIDTH == 5) begin
                 cyclonev_lcell_comb #(.lut_mask({2{LUT}}), .shared_arith("off"), .extended_lut("off"))
                 _TECHMAP_REPLACE_
                   (.combout(Y),
                    .dataa(A[0]),
                    .datab(A[1]),
                    .datac(A[2]),
                    .datad(A[3]),
                    .datae(A[4]),
                    .dataf(VCC),
                    .datag(VCC));
              end
              else
                if(WIDTH == 6) begin
                   cyclonev_lcell_comb #(.lut_mask(LUT), .shared_arith("off"), .extended_lut("off"))
                   _TECHMAP_REPLACE_
                     (.combout(Y),
                      .dataa(A[0]),
                      .datab(A[1]),
                      .datac(A[2]),
                      .datad(A[3]),
                      .datae(A[4]),
                      .dataf(A[5]),
                      .datag(VCC));
                end
                /*else
                  if(WIDTH == 7) begin
                    TODO: There's not a just 7-input function on Cyclone V, see the following note:
                    **Extended LUT Mode**
                    Use extended LUT mode to implement a specific set of 7-input functions. The set must
                    be a 2-to-1 multiplexer fed by two arbitrary 5-input functions sharing four inputs.
                    [source](Device Interfaces and Integration Basics for Cyclone V Devices).
                  end*/
                  else
                     wire _TECHMAP_FAIL_ = 1;
   endgenerate
endmodule // lut


