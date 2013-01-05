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
// *File Name: omsp_and_gate.v
// 
// *Module Description:
//                       Generic AND gate cell for the openMSP430
//
// *Author(s):
//              - Olivier Girard,    olgirard@gmail.com
//
//----------------------------------------------------------------------------
// $Rev: 103 $
// $LastChangedBy: olivier.girard $
// $LastChangedDate: 2011-03-05 15:44:48 +0100 (Sat, 05 Mar 2011) $
//----------------------------------------------------------------------------

module  omsp_and_gate (

// OUTPUTs
    y,                         // AND gate output

// INPUTs
    a,                         // AND gate input A
    b                          // AND gate input B
);

// OUTPUTs
//=========
output         y;              // AND gate output

// INPUTs
//=========
input          a;              // AND gate input A
input          b;              // AND gate input B


//=============================================================================
// 1)  SOME COMMENTS ON THIS MODULE
//=============================================================================
//
//    In its ASIC version, some combinatorial pathes of the openMSP430 are
// sensitive to glitches, in particular the ones generating the wakeup
// signals.
//    To prevent synthesis from optmizing combinatorial clouds into glitchy
// logic, this AND gate module has been instanciated in the critical places.
//
//    Make sure that synthesis doesn't ungroup this module. As an alternative,
// a standard cell from the library could also be directly instanciated here
// (don't forget the "dont_touch" attribute)
//
//
//=============================================================================
// 2)  AND GATE
//=============================================================================

assign  y  =  a & b;


endmodule // omsp_and_gate



