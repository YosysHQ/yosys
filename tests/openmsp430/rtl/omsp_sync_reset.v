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
// *File Name: omsp_sync_reset.v
// 
// *Module Description:
//                       Generic reset synchronizer for the openMSP430
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 103 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2011-03-05 15:44:48 +0100 (Sat, 05 Mar 2011) $
//----------------------------------------------------------------------------

module  omsp_sync_reset (

// OUTPUTs
    rst_s,                        // Synchronized reset

// INPUTs
    clk,                          // Receiving clock
    rst_a                         // Asynchronous reset
);

// OUTPUTs
//=========
output              rst_s;        // Synchronized reset

// INPUTs
//=========
input               clk;          // Receiving clock
input               rst_a;        // Asynchronous reset


//=============================================================================
// 1)  SYNCHRONIZER
//=============================================================================

reg    [1:0] data_sync;

always @(posedge clk or posedge rst_a)
  if (rst_a) data_sync <=  2'b11;
  else       data_sync <=  {data_sync[0], 1'b0};

assign       rst_s      =   data_sync[1];


endmodule // omsp_sync_reset

