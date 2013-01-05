//----------------------------------------------------------------------------
// Copyright (C) 2009 , Olivier Girard
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the authors nor the names of its contributors
//       may be used to endorse or promote products derived from this software
//       without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
// OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
// THE POSSIBILITY OF SUCH DAMAGE
//
//----------------------------------------------------------------------------
//
// *File Name: omsp_wakeup_cell.v
// 
// *Module Description:
//                       Generic Wakeup cell
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 103 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2011-03-05 15:44:48 +0100 (Sat, 05 Mar 2011) $
//----------------------------------------------------------------------------

module  omsp_wakeup_cell (

// OUTPUTs
    wkup_out,                  // Wakup signal (asynchronous)

// INPUTs
    scan_clk,                  // Scan clock
    scan_mode,                 // Scan mode
    scan_rst,                  // Scan reset
    wkup_clear,                // Glitch free wakeup event clear
    wkup_event                 // Glitch free asynchronous wakeup event
);

// OUTPUTs
//=========
output         wkup_out;       // Wakup signal (asynchronous)

// INPUTs
//=========
input          scan_clk;       // Scan clock
input          scan_mode;      // Scan mode
input          scan_rst;       // Scan reset
input          wkup_clear;     // Glitch free wakeup event clear
input          wkup_event;     // Glitch free asynchronous wakeup event


//=============================================================================
// 1)  AND GATE
//=============================================================================

// Scan stuff for the ASIC mode
`ifdef ASIC
   wire wkup_rst;
   omsp_scan_mux scan_mux_rst (
                               .scan_mode    (scan_mode),
                               .data_in_scan (scan_rst),
                               .data_in_func (wkup_clear),
                               .data_out     (wkup_rst)
   );

   wire wkup_clk;
   omsp_scan_mux scan_mux_clk (
                               .scan_mode    (scan_mode),
                               .data_in_scan (scan_clk),
                               .data_in_func (wkup_event),
                               .data_out     (wkup_clk)
   );

`else
   wire wkup_rst  =  wkup_clear;
   wire wkup_clk  =  wkup_event;
`endif

// Wakeup capture
reg    wkup_out;
always @(posedge wkup_clk or posedge wkup_rst)
  if (wkup_rst) wkup_out <= 1'b0;
  else          wkup_out <= 1'b1;


endmodule // omsp_wakeup_cell




