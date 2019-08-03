module EFX_LUT4(
   output O, 
   input I0,
   input I1,
   input I2,
   input I3
);
   parameter LUTMASK  = 16'h0000;
endmodule

module EFX_ADD(
   output O,
   output CO,
   input I0,
   input I1,
   input CI
);
   parameter I0_POLARITY   = 1;
   parameter I1_POLARITY   = 1;
endmodule

module EFX_FF(
   output Q,
   input D,
   input CE,
   input CLK,
   input SR
);
   parameter CLK_POLARITY = 1;
   parameter CE_POLARITY = 1;
   parameter SR_POLARITY = 1;
   parameter SR_SYNC = 0;
   parameter SR_VALUE = 0;
   parameter SR_SYNC_PRIORITY = 0;
   parameter D_POLARITY = 1;
endmodule