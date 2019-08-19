module \$__ALTSYNCRAM_SDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

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
   input  [CFG_ABITS-1:0] A1ADDR;
   input                  A1EN;
   //Write data
   output [CFG_DBITS-1:0] B1DATA;
   input  [CFG_ABITS-1:0] B1ADDR;
   input                  B1EN;

   wire [CFG_DBITS-1:0]   B1DATA_t;

   altsyncram  #(.clock_enable_input_b           ("ALTERNATE"   ),
                 .clock_enable_input_a           ("ALTERNATE"   ),
                 .clock_enable_output_b          ("NORMAL"      ),
                 .clock_enable_output_a          ("NORMAL"      ),
                 .wrcontrol_aclr_a               ("NONE"        ),
                 .indata_aclr_a                  ("NONE"        ),
                 .address_aclr_a                 ("NONE"        ),
                 .outdata_aclr_a                 ("NONE"        ),
                 .outdata_reg_a                  ("UNREGISTERED"),
                 .operation_mode                 ("DUAL_PORT"   ),
                 .intended_device_family         ("CYCLONE IVE" ),
                 .outdata_reg_a                  ("UNREGISTERED"),
                 .lpm_type                       ("altsyncram"  ),
                 .init_type                      ("unused"      ),
                 .ram_block_type                 ("AUTO"        ),
                 .lpm_hint                       ("ENABLE_RUNTIME_MOD=NO"), // Forced value
                 .power_up_uninitialized         ("FALSE"       ),
                 .read_during_write_mode_port_a  ("NEW_DATA_NO_NBE_READ"), // Forced value
                 .width_byteena_a                (   1          ), // Forced value
                 .numwords_b                     ( 2**CFG_ABITS ),
                 .numwords_a                     ( 2**CFG_ABITS ),
                 .widthad_b                      ( CFG_ABITS    ),
                 .width_b                        ( CFG_DBITS    ),
                 .widthad_a                      ( CFG_ABITS    ),
                 .width_a                        ( CFG_DBITS    )
                 ) _TECHMAP_REPLACE_ (
                                      .data_a(A1DATA),
                                      .address_a(A1ADDR),
                                      .wren_a(A1EN),
                                      .rden_a(1'b0),
                                      .q_a(),
                                      .data_b({CFG_DBITS{1'b0}}),
                                      .address_b(B1ADDR),
                                      .wren_b(1'b0),
                                      .rden_b(B1EN),
                                      .q_b(B1DATA),
                                      .clock0(CLK2),
                                      .clock1(1'b0), // Unused in sdp mode
                                      .clocken0(1'b1),
                                      .clocken1(1'b1),
                                      .clocken2(1'b1),
                                      .clocken3(1'b1),
                                      .aclr0(1'b0),
                                      .aclr1(1'b0),
                                      .addressstall_a(1'b0),
                                      .addressstall_b(1'b0));

endmodule

