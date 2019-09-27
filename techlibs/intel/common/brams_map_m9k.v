module \$__M9K_ALTSYNCRAM_SINGLEPORT_FULL (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

   parameter CFG_ABITS = 8;
   parameter CFG_DBITS = 36;
   parameter ABITS = 1;
   parameter DBITS = 1;
   parameter CLKPOL2 = 1;
   parameter CLKPOL3 = 1;

   input CLK2;
   input CLK3;
   //Read data
   output [CFG_DBITS-1:0] A1DATA;
   input [CFG_ABITS-1:0]  A1ADDR;
   input                  A1EN;
   //Write data
   output [CFG_DBITS-1:0] B1DATA;
   input [CFG_ABITS-1:0]  B1ADDR;
   input                  B1EN;

   wire [CFG_DBITS-1:0]   B1DATA_t;

   localparam MODE = CFG_DBITS == 1  ? 1:
                     CFG_DBITS == 2  ? 2:
                     CFG_DBITS == 4  ? 3:
                     CFG_DBITS == 8  ? 4:
                     CFG_DBITS == 9  ? 5:
                     CFG_DBITS == 16 ? 6:
                     CFG_DBITS == 18 ? 7:
                     CFG_DBITS == 32 ? 8:
                     CFG_DBITS == 36 ? 9:
                     'bx;

   localparam NUMWORDS = CFG_DBITS == 1  ? 8192:
                         CFG_DBITS == 2  ? 4096:
                         CFG_DBITS == 4  ? 2048:
                         CFG_DBITS == 8  ? 1024:
                         CFG_DBITS == 9  ? 1024:
                         CFG_DBITS == 16 ?  512:
                         CFG_DBITS == 18 ?  512:
                         CFG_DBITS == 32 ?  256:
                         CFG_DBITS == 36 ?  256:
                         'bx;

   altsyncram  #(.clock_enable_input_b           ("ALTERNATE"   ),
                 .clock_enable_input_a           ("ALTERNATE"   ),
                 .clock_enable_output_b          ("NORMAL"      ),
                 .clock_enable_output_a          ("NORMAL"      ),
                 .wrcontrol_aclr_a               ("NONE"        ),
                 .indata_aclr_a                  ("NONE"        ),
                 .address_aclr_a                 ("NONE"        ),
                 .outdata_aclr_a                 ("NONE"        ),
                 .outdata_reg_a                  ("UNREGISTERED"),
                 .operation_mode                 ("SINGLE_PORT" ),
                 .intended_device_family         ("CYCLONE IVE" ),
                 .outdata_reg_a                  ("UNREGISTERED"),
                 .lpm_type                       ("altsyncram"  ),
                 .init_type                      ("unused"      ),
                 .ram_block_type                 ("AUTO"        ),
                 .lpm_hint                       ("ENABLE_RUNTIME_MOD=NO"), // Forced value
                 .power_up_uninitialized         ("FALSE"),
                 .read_during_write_mode_port_a  ("NEW_DATA_NO_NBE_READ"), // Forced value
                 .width_byteena_a                (1), // Forced value
                 .numwords_b                     ( NUMWORDS     ),
                 .numwords_a                     ( NUMWORDS     ),
                 .widthad_b                      ( CFG_DBITS    ),
                 .width_b                        ( CFG_ABITS    ),
                 .widthad_a                      ( CFG_DBITS    ),
                 .width_a                        ( CFG_ABITS    )
                 ) _TECHMAP_REPLACE_ (
                                      .data_a(B1DATA),
                                      .address_a(B1ADDR),
                                      .wren_a(B1EN),
                                      .rden_a(A1EN),
                                      .q_a(A1DATA),
                                      .data_b(B1DATA),
                                      .address_b(0),
                                      .wren_b(1'b0),
                                      .rden_b(1'b0),
                                      .q_b(),
                                      .clock0(CLK2),
                                      .clock1(1'b1), // Unused in single port mode
                                      .clocken0(1'b1),
                                      .clocken1(1'b1),
                                      .clocken2(1'b1),
                                      .clocken3(1'b1),
                                      .aclr0(1'b0),
                                      .aclr1(1'b0),
                                      .addressstall_a(1'b0),
                                      .addressstall_b(1'b0));

endmodule

