/////////////////////////////////////////////////////////////////////
////                                                             ////
////  AES Inverse SBOX (ROM)                                     ////
////                                                             ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
////                                                             ////
////  Downloaded from: http://www.opencores.org/cores/aes_core/  ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2000-2002 Rudolf Usselmann                    ////
////                         www.asics.ws                        ////
////                         rudi@asics.ws                       ////
////                                                             ////
//// This source file may be used and distributed without        ////
//// restriction provided that this copyright statement is not   ////
//// removed from the file and that any derivative work contains ////
//// the original copyright notice and the associated disclaimer.////
////                                                             ////
////     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ////
//// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ////
//// TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ////
//// FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ////
//// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ////
//// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ////
//// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ////
//// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ////
//// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ////
//// LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ////
//// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ////
//// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ////
//// POSSIBILITY OF SUCH DAMAGE.                                 ////
////                                                             ////
/////////////////////////////////////////////////////////////////////

//  CVS Log
//
//  $Id: aes_inv_sbox.v,v 1.1.1.1 2002/11/09 11:22:55 rudi Exp $
//
//  $Date: 2002/11/09 11:22:55 $
//  $Revision: 1.1.1.1 $
//  $Author: rudi $
//  $Locker:  $
//  $State: Exp $
//
// Change History:
//               $Log: aes_inv_sbox.v,v $
//               Revision 1.1.1.1  2002/11/09 11:22:55  rudi
//               Initial Checkin
//
//
//
//
//
//

`include "timescale.v"

module aes_inv_sbox(a,d);
input	[7:0]	a;
output	[7:0]	d;
reg	[7:0]	d;

always @(a)
	case(a)		// synopsys full_case parallel_case
	   8'h00: d=8'h52;
	   8'h01: d=8'h09;
	   8'h02: d=8'h6a;
	   8'h03: d=8'hd5;
	   8'h04: d=8'h30;
	   8'h05: d=8'h36;
	   8'h06: d=8'ha5;
	   8'h07: d=8'h38;
	   8'h08: d=8'hbf;
	   8'h09: d=8'h40;
	   8'h0a: d=8'ha3;
	   8'h0b: d=8'h9e;
	   8'h0c: d=8'h81;
	   8'h0d: d=8'hf3;
	   8'h0e: d=8'hd7;
	   8'h0f: d=8'hfb;
	   8'h10: d=8'h7c;
	   8'h11: d=8'he3;
	   8'h12: d=8'h39;
	   8'h13: d=8'h82;
	   8'h14: d=8'h9b;
	   8'h15: d=8'h2f;
	   8'h16: d=8'hff;
	   8'h17: d=8'h87;
	   8'h18: d=8'h34;
	   8'h19: d=8'h8e;
	   8'h1a: d=8'h43;
	   8'h1b: d=8'h44;
	   8'h1c: d=8'hc4;
	   8'h1d: d=8'hde;
	   8'h1e: d=8'he9;
	   8'h1f: d=8'hcb;
	   8'h20: d=8'h54;
	   8'h21: d=8'h7b;
	   8'h22: d=8'h94;
	   8'h23: d=8'h32;
	   8'h24: d=8'ha6;
	   8'h25: d=8'hc2;
	   8'h26: d=8'h23;
	   8'h27: d=8'h3d;
	   8'h28: d=8'hee;
	   8'h29: d=8'h4c;
	   8'h2a: d=8'h95;
	   8'h2b: d=8'h0b;
	   8'h2c: d=8'h42;
	   8'h2d: d=8'hfa;
	   8'h2e: d=8'hc3;
	   8'h2f: d=8'h4e;
	   8'h30: d=8'h08;
	   8'h31: d=8'h2e;
	   8'h32: d=8'ha1;
	   8'h33: d=8'h66;
	   8'h34: d=8'h28;
	   8'h35: d=8'hd9;
	   8'h36: d=8'h24;
	   8'h37: d=8'hb2;
	   8'h38: d=8'h76;
	   8'h39: d=8'h5b;
	   8'h3a: d=8'ha2;
	   8'h3b: d=8'h49;
	   8'h3c: d=8'h6d;
	   8'h3d: d=8'h8b;
	   8'h3e: d=8'hd1;
	   8'h3f: d=8'h25;
	   8'h40: d=8'h72;
	   8'h41: d=8'hf8;
	   8'h42: d=8'hf6;
	   8'h43: d=8'h64;
	   8'h44: d=8'h86;
	   8'h45: d=8'h68;
	   8'h46: d=8'h98;
	   8'h47: d=8'h16;
	   8'h48: d=8'hd4;
	   8'h49: d=8'ha4;
	   8'h4a: d=8'h5c;
	   8'h4b: d=8'hcc;
	   8'h4c: d=8'h5d;
	   8'h4d: d=8'h65;
	   8'h4e: d=8'hb6;
	   8'h4f: d=8'h92;
	   8'h50: d=8'h6c;
	   8'h51: d=8'h70;
	   8'h52: d=8'h48;
	   8'h53: d=8'h50;
	   8'h54: d=8'hfd;
	   8'h55: d=8'hed;
	   8'h56: d=8'hb9;
	   8'h57: d=8'hda;
	   8'h58: d=8'h5e;
	   8'h59: d=8'h15;
	   8'h5a: d=8'h46;
	   8'h5b: d=8'h57;
	   8'h5c: d=8'ha7;
	   8'h5d: d=8'h8d;
	   8'h5e: d=8'h9d;
	   8'h5f: d=8'h84;
	   8'h60: d=8'h90;
	   8'h61: d=8'hd8;
	   8'h62: d=8'hab;
	   8'h63: d=8'h00;
	   8'h64: d=8'h8c;
	   8'h65: d=8'hbc;
	   8'h66: d=8'hd3;
	   8'h67: d=8'h0a;
	   8'h68: d=8'hf7;
	   8'h69: d=8'he4;
	   8'h6a: d=8'h58;
	   8'h6b: d=8'h05;
	   8'h6c: d=8'hb8;
	   8'h6d: d=8'hb3;
	   8'h6e: d=8'h45;
	   8'h6f: d=8'h06;
	   8'h70: d=8'hd0;
	   8'h71: d=8'h2c;
	   8'h72: d=8'h1e;
	   8'h73: d=8'h8f;
	   8'h74: d=8'hca;
	   8'h75: d=8'h3f;
	   8'h76: d=8'h0f;
	   8'h77: d=8'h02;
	   8'h78: d=8'hc1;
	   8'h79: d=8'haf;
	   8'h7a: d=8'hbd;
	   8'h7b: d=8'h03;
	   8'h7c: d=8'h01;
	   8'h7d: d=8'h13;
	   8'h7e: d=8'h8a;
	   8'h7f: d=8'h6b;
	   8'h80: d=8'h3a;
	   8'h81: d=8'h91;
	   8'h82: d=8'h11;
	   8'h83: d=8'h41;
	   8'h84: d=8'h4f;
	   8'h85: d=8'h67;
	   8'h86: d=8'hdc;
	   8'h87: d=8'hea;
	   8'h88: d=8'h97;
	   8'h89: d=8'hf2;
	   8'h8a: d=8'hcf;
	   8'h8b: d=8'hce;
	   8'h8c: d=8'hf0;
	   8'h8d: d=8'hb4;
	   8'h8e: d=8'he6;
	   8'h8f: d=8'h73;
	   8'h90: d=8'h96;
	   8'h91: d=8'hac;
	   8'h92: d=8'h74;
	   8'h93: d=8'h22;
	   8'h94: d=8'he7;
	   8'h95: d=8'had;
	   8'h96: d=8'h35;
	   8'h97: d=8'h85;
	   8'h98: d=8'he2;
	   8'h99: d=8'hf9;
	   8'h9a: d=8'h37;
	   8'h9b: d=8'he8;
	   8'h9c: d=8'h1c;
	   8'h9d: d=8'h75;
	   8'h9e: d=8'hdf;
	   8'h9f: d=8'h6e;
	   8'ha0: d=8'h47;
	   8'ha1: d=8'hf1;
	   8'ha2: d=8'h1a;
	   8'ha3: d=8'h71;
	   8'ha4: d=8'h1d;
	   8'ha5: d=8'h29;
	   8'ha6: d=8'hc5;
	   8'ha7: d=8'h89;
	   8'ha8: d=8'h6f;
	   8'ha9: d=8'hb7;
	   8'haa: d=8'h62;
	   8'hab: d=8'h0e;
	   8'hac: d=8'haa;
	   8'had: d=8'h18;
	   8'hae: d=8'hbe;
	   8'haf: d=8'h1b;
	   8'hb0: d=8'hfc;
	   8'hb1: d=8'h56;
	   8'hb2: d=8'h3e;
	   8'hb3: d=8'h4b;
	   8'hb4: d=8'hc6;
	   8'hb5: d=8'hd2;
	   8'hb6: d=8'h79;
	   8'hb7: d=8'h20;
	   8'hb8: d=8'h9a;
	   8'hb9: d=8'hdb;
	   8'hba: d=8'hc0;
	   8'hbb: d=8'hfe;
	   8'hbc: d=8'h78;
	   8'hbd: d=8'hcd;
	   8'hbe: d=8'h5a;
	   8'hbf: d=8'hf4;
	   8'hc0: d=8'h1f;
	   8'hc1: d=8'hdd;
	   8'hc2: d=8'ha8;
	   8'hc3: d=8'h33;
	   8'hc4: d=8'h88;
	   8'hc5: d=8'h07;
	   8'hc6: d=8'hc7;
	   8'hc7: d=8'h31;
	   8'hc8: d=8'hb1;
	   8'hc9: d=8'h12;
	   8'hca: d=8'h10;
	   8'hcb: d=8'h59;
	   8'hcc: d=8'h27;
	   8'hcd: d=8'h80;
	   8'hce: d=8'hec;
	   8'hcf: d=8'h5f;
	   8'hd0: d=8'h60;
	   8'hd1: d=8'h51;
	   8'hd2: d=8'h7f;
	   8'hd3: d=8'ha9;
	   8'hd4: d=8'h19;
	   8'hd5: d=8'hb5;
	   8'hd6: d=8'h4a;
	   8'hd7: d=8'h0d;
	   8'hd8: d=8'h2d;
	   8'hd9: d=8'he5;
	   8'hda: d=8'h7a;
	   8'hdb: d=8'h9f;
	   8'hdc: d=8'h93;
	   8'hdd: d=8'hc9;
	   8'hde: d=8'h9c;
	   8'hdf: d=8'hef;
	   8'he0: d=8'ha0;
	   8'he1: d=8'he0;
	   8'he2: d=8'h3b;
	   8'he3: d=8'h4d;
	   8'he4: d=8'hae;
	   8'he5: d=8'h2a;
	   8'he6: d=8'hf5;
	   8'he7: d=8'hb0;
	   8'he8: d=8'hc8;
	   8'he9: d=8'heb;
	   8'hea: d=8'hbb;
	   8'heb: d=8'h3c;
	   8'hec: d=8'h83;
	   8'hed: d=8'h53;
	   8'hee: d=8'h99;
	   8'hef: d=8'h61;
	   8'hf0: d=8'h17;
	   8'hf1: d=8'h2b;
	   8'hf2: d=8'h04;
	   8'hf3: d=8'h7e;
	   8'hf4: d=8'hba;
	   8'hf5: d=8'h77;
	   8'hf6: d=8'hd6;
	   8'hf7: d=8'h26;
	   8'hf8: d=8'he1;
	   8'hf9: d=8'h69;
	   8'hfa: d=8'h14;
	   8'hfb: d=8'h63;
	   8'hfc: d=8'h55;
	   8'hfd: d=8'h21;
	   8'hfe: d=8'h0c;
	   8'hff: d=8'h7d;
	endcase
endmodule


