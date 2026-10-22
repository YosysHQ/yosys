`default_nettype none
module latch_002_gate (dword, vect, sel, st);
   output reg [63:0] dword;
   input wire [7:0]  vect;
   input wire [7:0]  sel;
   input 	     st;
   always @*
     case (|(st))
       1'b 1:
         case ((((8)*(sel)))+(0))
           0:
             dword[7:0] <= vect[7:0];
           1:
             dword[8:1] <= vect[7:0];
           2:
             dword[9:2] <= vect[7:0];
           3:
             dword[10:3] <= vect[7:0];
           4:
             dword[11:4] <= vect[7:0];
           5:
             dword[12:5] <= vect[7:0];
           6:
             dword[13:6] <= vect[7:0];
           7:
             dword[14:7] <= vect[7:0];
           8:
             dword[15:8] <= vect[7:0];
           9:
             dword[16:9] <= vect[7:0];
           10:
             dword[17:10] <= vect[7:0];
           11:
             dword[18:11] <= vect[7:0];
           12:
             dword[19:12] <= vect[7:0];
           13:
             dword[20:13] <= vect[7:0];
           14:
             dword[21:14] <= vect[7:0];
           15:
             dword[22:15] <= vect[7:0];
           16:
             dword[23:16] <= vect[7:0];
           17:
             dword[24:17] <= vect[7:0];
           18:
             dword[25:18] <= vect[7:0];
           19:
             dword[26:19] <= vect[7:0];
           20:
             dword[27:20] <= vect[7:0];
           21:
             dword[28:21] <= vect[7:0];
           22:
             dword[29:22] <= vect[7:0];
           23:
             dword[30:23] <= vect[7:0];
           24:
             dword[31:24] <= vect[7:0];
           25:
             dword[32:25] <= vect[7:0];
           26:
             dword[33:26] <= vect[7:0];
           27:
             dword[34:27] <= vect[7:0];
           28:
             dword[35:28] <= vect[7:0];
           29:
             dword[36:29] <= vect[7:0];
           30:
             dword[37:30] <= vect[7:0];
           31:
             dword[38:31] <= vect[7:0];
           32:
             dword[39:32] <= vect[7:0];
           33:
             dword[40:33] <= vect[7:0];
           34:
             dword[41:34] <= vect[7:0];
           35:
             dword[42:35] <= vect[7:0];
           36:
             dword[43:36] <= vect[7:0];
           37:
             dword[44:37] <= vect[7:0];
           38:
             dword[45:38] <= vect[7:0];
           39:
             dword[46:39] <= vect[7:0];
           40:
             dword[47:40] <= vect[7:0];
           41:
             dword[48:41] <= vect[7:0];
           42:
             dword[49:42] <= vect[7:0];
           43:
             dword[50:43] <= vect[7:0];
           44:
             dword[51:44] <= vect[7:0];
           45:
             dword[52:45] <= vect[7:0];
           46:
             dword[53:46] <= vect[7:0];
           47:
             dword[54:47] <= vect[7:0];
           48:
             dword[55:48] <= vect[7:0];
           49:
             dword[56:49] <= vect[7:0];
           50:
             dword[57:50] <= vect[7:0];
           51:
             dword[58:51] <= vect[7:0];
           52:
             dword[59:52] <= vect[7:0];
           53:
             dword[60:53] <= vect[7:0];
           54:
             dword[61:54] <= vect[7:0];
           55:
             dword[62:55] <= vect[7:0];
           56:
             dword[63:56] <= vect[7:0];
           57:
             dword[63:57] <= vect[7:0];
           58:
             dword[63:58] <= vect[7:0];
           59:
             dword[63:59] <= vect[7:0];
           60:
             dword[63:60] <= vect[7:0];
           61:
             dword[63:61] <= vect[7:0];
           62:
             dword[63:62] <= vect[7:0];
           63:
             dword[63:63] <= vect[7:0];
         endcase
     endcase
endmodule
