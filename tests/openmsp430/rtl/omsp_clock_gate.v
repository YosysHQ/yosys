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
// *File Name: omsp_clock_gate.v
// 
// *Module Description:
//                       Generic clock gate cell for the openMSP430
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 103 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2011-03-05 15:44:48 +0100 (Sat, 05 Mar 2011) $
//----------------------------------------------------------------------------

module  omsp_clock_gate (

// OUTPUTs
    gclk,                      // Gated clock

// INPUTs
    clk,                       // Clock
    enable,                    // Clock enable
    scan_enable                // Scan enable (active during scan shifting)
);

// OUTPUTs
//=========
output         gclk;           // Gated clock

// INPUTs
//=========
input          clk;            // Clock
input          enable;         // Clock enable
input          scan_enable;    // Scan enable (active during scan shifting)


//=============================================================================
// CLOCK GATE: LATCH + AND
//=============================================================================
   
// Enable clock gate during scan shift
// (the gate itself is checked with the scan capture cycle)
wire    enable_in =   (enable | scan_enable);

// LATCH the enable signal
reg     enable_latch;
always @(clk or enable_in)
  if (~clk)
    enable_latch <= enable_in;

// AND gate
assign  gclk      =  (clk & enable_latch);


endmodule // omsp_clock_gate


