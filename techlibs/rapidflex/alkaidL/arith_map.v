// Arithmetic units: adder
// Adapt from:  https://github.com/chipsalliance/yosys-f4pga-plugins/blob/0ad1af26a29243a9e76379943d735e119dcd0cc6/ql-qlf-plugin/qlf_k6n10/cells_sim.v
// Many thanks to F4PGA for their contribution

(* techmap_celltype = "$alu" *)
module _80_quicklogic_alu (A, B, CI, BI, X, Y, CO);

	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	output [Y_WIDTH-1:0] CO;

    // The max. number of adders we can support in AlkaidS is (12x2-1)x4x16 = 1472
    // Fail when resource limit exceeds
    // Also fail when a low utilization rate is detected
    // Originally prefer to defer carry mapping when < 2-bit adder is detected
    // Due to a bug found in scalable seq detector, the bound is increased to 4-bit adder
    wire _TECHMAP_FAIL_ = Y_WIDTH > 1472 || Y_WIDTH < 4;
    generate
      if ((A_WIDTH == 0 || B_WIDTH == 0) && Y_WIDTH > 0) begin
        wire _TECHMAP_FAIL_ = 1;
      end
    endgenerate 
	wire [1024:0] _TECHMAP_DO_ = "splitnets CARRY; clean";
    localparam Y_COL_WIDTH = 96 - 3; 
    localparam Y_MAX_WIDTH = 12 - 3; 

        (* force_downto *)
        wire [Y_WIDTH-1:0] A_buf, B_buf;
        \$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
        \$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

        (* force_downto *)
        wire [Y_WIDTH-1:0] AA = A_buf;
        (* force_downto *)
        wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;
	wire [Y_WIDTH: 0] CARRY;

	assign CO[Y_WIDTH-1:0] = CARRY[Y_WIDTH:1];
    genvar i;
    generate if (Y_WIDTH < Y_COL_WIDTH) begin 
         wire CARRY_end_buf;
	     wire [1024:0] _TECHMAP_DO_ = "insbuf CARRY[Y_WIDTH] CARRY_end_buf";
	     _fpga_adder intermediate_adder (
	       .cin     ( ),
	       .cout    (CARRY[0]),
	       .a       (CI     ),
	       .b       (CI     ),
	       .sumout  (      )
	     );

	     _fpga_adder first_adder (
	       .cin     (CARRY[0]),
	       .cout    (CARRY[1]),
	       .a       (AA[0]  ),
	       .b       (BB[0]  ),
	       .sumout  (Y[0]   )
	     );

    	 _fpga_adder pretaill_adder (
    	   .cin     (CARRY[Y_WIDTH-1]  ),
    	   .cout    (CARRY_end_buf),
    	   .a       (AA[Y_WIDTH-1]     ),
    	   .b       (BB[Y_WIDTH-1]     ),
    	   .sumout  (Y[Y_WIDTH-1]      )
    	 );


  	    _fpga_adder tail_adder (
  	      .cin     (CARRY_end_buf),
  	      .cout    (),
  	      .a       (1'b0),
  	      .b       (1'b0),
  	      .sumout  (CARRY[Y_WIDTH])
  	    );
    
    	generate for (i = 1; i < Y_WIDTH-1 ; i = i+1) begin:gen3
    	     _fpga_adder my_adder (
    	       .cin     (CARRY[i]  ),
    	       .cout    (CARRY[i+1]),
    	       .a       (AA[i]     ),
    	       .b       (BB[i]     ),
    	       .sumout  (Y[i]      )
    	     );
    	end endgenerate
    end else begin
	    generate for (i = 0; i < Y_WIDTH ; i = i+1) begin:gen4
  	        // Due to VPR limitations regarding IO connexion to carry chain,
  	        // we generate the carry chain input signal using an intermediate adder
  	        // since we can connect a & b from io pads, but not cin & cout
            if (i == 0) begin
  	             _fpga_adder intermediate_adder (
  	               .cin     ( ),
  	               .cout    (CARRY[0]),
  	               .a       (CI     ),
  	               .b       (CI     ),
  	               .sumout  (      )
  	             );
  
  	             _fpga_adder first_adder (
  	               .cin     (CARRY[0]),
  	               .cout    (CARRY[1]),
  	               .a       (AA[0]  ),
  	               .b       (BB[0]  ),
  	               .sumout  (Y[0]   )
  	             );
            end else if (i % (Y_MAX_WIDTH + 1) == 0) begin
                 wire CARRY_end_buf;
                 wire CARRY_start_buf;
	             wire [1024:0] _TECHMAP_DO_ = "insbuf CARRY[i+1] CARRY_end_buf; insbuf CARRY_end_buf CARRY_start_buf";
  	             _fpga_adder tail_adder (
  	               .cin     (CARRY[i]),
  	               .cout    (),
  	               .a       (1'b0),
  	               .b       (1'b0),
  	               .sumout  (CARRY_end_buf)
  	             );

  	             _fpga_adder intermediate_adder (
  	               .cin     ( ),
  	               .cout    (CARRY_start_buf),
  	               .a       (CARRY_end_buf),
  	               .b       (1'b1),
  	               .sumout  (      )
  	             );
  
  	             _fpga_adder first_adder (
  	               .cin     (CARRY_start_buf),
  	               .cout    (CARRY[i+1]),
  	               .a       (AA[i]  ),
  	               .b       (BB[i]  ),
  	               .sumout  (Y[i]   )
  	             );
            end else begin
	            _fpga_adder my_adder (
	              .cin     (CARRY[i]  ),
	              .cout    (CARRY[i+1]),
	              .a       (AA[i]     ),
	              .b       (BB[i]     ),
	              .sumout  (Y[i]      )
	            );
            end
	    end endgenerate
	end endgenerate
	assign X = AA ^ BB;
endmodule
