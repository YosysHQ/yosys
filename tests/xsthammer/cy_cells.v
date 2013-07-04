
// Based on the simulation models from /opt/altera/13.0/quartus/eda/sim_lib/cycloneiii_atoms.v

module cycloneiii_lcell_comb (dataa, datab, datac, datad, cin, combout, cout);

input dataa, datab, datac, datad, cin;
output combout, cout;

parameter lut_mask = 16'hFFFF;
parameter sum_lutc_input = "datac";
parameter dont_touch = "off";
parameter lpm_type = "cycloneiii_lcell_comb";

reg cout_tmp, combout_tmp;
reg [1:0] isum_lutc_input;

// 4-input LUT function
function lut4;
	input [15:0] mask;
	input dataa, datab, datac, datad;
	begin
	    lut4 = datad ? ( datac ? ( datab ? ( dataa ? mask[15] : mask[14])
					     : ( dataa ? mask[13] : mask[12]))
				   : ( datab ? ( dataa ? mask[11] : mask[10])
					     : ( dataa ? mask[ 9] : mask[ 8])))
			 : ( datac ? ( datab ? ( dataa ? mask[ 7] : mask[ 6])
					     : ( dataa ? mask[ 5] : mask[ 4]))
				   : ( datab ? ( dataa ? mask[ 3] : mask[ 2])
					     : ( dataa ? mask[ 1] : mask[ 0])));
	end
endfunction

initial
	if (sum_lutc_input == "datac")
		isum_lutc_input = 0;
	else if (sum_lutc_input == "cin")
		isum_lutc_input = 1;
	else
		isum_lutc_input = 2;

always @* begin
	if (isum_lutc_input == 0) // datac 
		combout_tmp = lut4(lut_mask, dataa, datab, datac, datad);
	else if (isum_lutc_input == 1) // cin
		combout_tmp = lut4(lut_mask, dataa, datab, cin, datad);
	cout_tmp = lut4(lut_mask, dataa, datab, cin, 'b0);
end

assign combout = combout_tmp;
assign cout = cout_tmp;

endmodule

// ----------------------------------------------------------------------

module cycloneiii_io_ibuf (i, ibar, o);

parameter differential_mode = "false";
parameter bus_hold = "false";
parameter simulate_z_as = "Z";
parameter lpm_type = "cycloneiii_io_ibuf";

input i, ibar;
output o;

assign o = i;

endmodule

// ----------------------------------------------------------------------

module cycloneiii_io_obuf (i, oe, seriesterminationcontrol, devoe, o, obar);

parameter open_drain_output = "false";
parameter bus_hold = "false";
parameter lpm_type = "cycloneiii_io_obuf";

input i, oe, devoe;
input [15:0] seriesterminationcontrol; 
output o, obar;

assign o = i;
assign obar = ~i;

endmodule

// ----------------------------------------------------------------------

module cycloneiii_mac_data_reg (clk,
                               data,
                               ena,
                               aclr,
                               dataout
                              );

    parameter data_width = 18;

    // INPUT PORTS
    input clk;
    input [17 : 0] data;
    input ena;
    input aclr;

    // OUTPUT PORTS
    output [17:0] dataout;

    // INTERNAL VARIABLES AND NETS
    reg clk_last_value;
    reg [17:0] dataout_tmp;
    wire [17:0] dataout_wire;

    // INTERNAL VARIABLES
    wire [17:0] data_ipd; 
    wire enable;
    wire no_clr;
    reg d_viol;
    reg ena_viol;
    wire clk_ipd;
    wire ena_ipd;
    wire aclr_ipd;

 
    // BUFFER INPUTS
    buf (clk_ipd, clk);
    buf (ena_ipd, ena);
    buf (aclr_ipd, aclr);

    buf (data_ipd[0], data[0]);
    buf (data_ipd[1], data[1]);
    buf (data_ipd[2], data[2]);
    buf (data_ipd[3], data[3]);
    buf (data_ipd[4], data[4]);
    buf (data_ipd[5], data[5]);
    buf (data_ipd[6], data[6]);
    buf (data_ipd[7], data[7]);
    buf (data_ipd[8], data[8]);
    buf (data_ipd[9], data[9]);
    buf (data_ipd[10], data[10]);
    buf (data_ipd[11], data[11]);
    buf (data_ipd[12], data[12]);
    buf (data_ipd[13], data[13]);
    buf (data_ipd[14], data[14]);
    buf (data_ipd[15], data[15]);
    buf (data_ipd[16], data[16]);
    buf (data_ipd[17], data[17]);

    assign enable = (!aclr_ipd) && (ena_ipd);
    assign no_clr = (!aclr_ipd);

    initial
    begin
        clk_last_value <= 'b0;
        dataout_tmp <= 18'b0;
    end

    always @(clk_ipd or aclr_ipd)
    begin
        if (d_viol == 1'b1 || ena_viol == 1'b1)
        begin
            dataout_tmp <= 'bX;
        end
        else if (aclr_ipd == 1'b1)
        begin
            dataout_tmp <= 'b0;
        end
        else 
        begin
            if ((clk_ipd === 1'b1) && (clk_last_value == 1'b0))
                if (ena_ipd === 1'b1)
                    dataout_tmp <= data_ipd;
        end

        clk_last_value <= clk_ipd;

    end // always

    assign dataout_wire = dataout_tmp;
      
    and (dataout[0], dataout_wire[0], 1'b1);
    and (dataout[1], dataout_wire[1], 1'b1);
    and (dataout[2], dataout_wire[2], 1'b1);
    and (dataout[3], dataout_wire[3], 1'b1);
    and (dataout[4], dataout_wire[4], 1'b1);
    and (dataout[5], dataout_wire[5], 1'b1);
    and (dataout[6], dataout_wire[6], 1'b1);
    and (dataout[7], dataout_wire[7], 1'b1);
    and (dataout[8], dataout_wire[8], 1'b1);
    and (dataout[9], dataout_wire[9], 1'b1);
    and (dataout[10], dataout_wire[10], 1'b1);
    and (dataout[11], dataout_wire[11], 1'b1);
    and (dataout[12], dataout_wire[12], 1'b1);
    and (dataout[13], dataout_wire[13], 1'b1);
    and (dataout[14], dataout_wire[14], 1'b1);
    and (dataout[15], dataout_wire[15], 1'b1);
    and (dataout[16], dataout_wire[16], 1'b1);
    and (dataout[17], dataout_wire[17], 1'b1);

endmodule //cycloneiii_mac_data_reg

module cycloneiii_mac_sign_reg (
                               clk,
                               d,
                               ena,
                               aclr,
                               q
                              );

    // INPUT PORTS
    input clk;
    input d;
    input ena;
    input aclr;
    
    // OUTPUT PORTS
    output q;
    
    // INTERNAL VARIABLES
    reg clk_last_value;
    reg q_tmp;
    reg ena_viol;
    reg d_viol;
    
    wire enable;
    
    // DEFAULT VALUES THRO' PULLUPs
    // tri1 aclr, ena;
    
    wire d_ipd;
    wire clk_ipd;
    wire ena_ipd;
    wire aclr_ipd;
    
    buf (d_ipd, d);
    buf (clk_ipd, clk);
    buf (ena_ipd, ena);
    buf (aclr_ipd, aclr);
    
    assign enable = (!aclr_ipd) && (ena_ipd);
    
    initial
    begin
        clk_last_value <= 'b0;
        q_tmp <= 'b0;
    end
    
        always @ (clk_ipd or aclr_ipd)
        begin
            if (d_viol == 1'b1 || ena_viol == 1'b1)
            begin
                q_tmp <= 'bX;
            end
            else
            begin
            if (aclr_ipd == 1'b1)
                q_tmp <= 0;
            else if ((clk_ipd == 1'b1) && (clk_last_value == 1'b0))
                if (ena_ipd == 1'b1)
                    q_tmp <= d_ipd;
            end
    
            clk_last_value <= clk_ipd;
        end
    
    and (q, q_tmp, 'b1);

endmodule // cycloneiii_mac_sign_reg

module cycloneiii_mac_mult_internal
   (
    dataa, 
    datab,
    signa, 
    signb,
    dataout
    );
    
    parameter dataa_width    = 18;
    parameter datab_width    = 18;
    parameter dataout_width  = dataa_width + datab_width;
    
    // INPUT
    input [dataa_width-1:0] dataa;
    input [datab_width-1:0] datab;
    input 	signa;
    input 	signb;
 
    // OUTPUT
    output [dataout_width-1:0] dataout;

    // Internal variables
    wire [17:0] dataa_ipd; 
    wire [17:0] datab_ipd;
    wire signa_ipd; 
    wire signb_ipd;

    wire [dataout_width-1:0] dataout_tmp; 
 
    wire ia_is_positive;
    wire ib_is_positive;
    wire [17:0] iabsa;		// absolute value (i.e. positive) form of dataa input
    wire [17:0] iabsb;		// absolute value (i.e. positive) form of datab input
    wire [35:0] iabsresult;	// absolute value (i.e. positive) form of product (a * b)
 
    
    reg [17:0] i_ones;		// padding with 1's for input negation

    // Input buffers
    buf (signa_ipd, signa);
    buf (signb_ipd, signb);

    // buf dataa_buf [dataa_width-1:0] (dataa_ipd[dataa_width-1:0], dataa);
    // buf datab_buf [datab_width-1:0] (datab_ipd[datab_width-1:0], datab);
    assign dataa_ipd[dataa_width-1:0] = dataa;
    assign datab_ipd[datab_width-1:0] = datab;

    initial
    begin
        // 1's padding for 18-bit wide inputs
        i_ones = ~0;
    end
    
    // get signs of a and b, and get absolute values since Verilog '*' operator
    // is an unsigned multiplication
    assign ia_is_positive = ~signa_ipd | ~dataa_ipd[dataa_width-1];
    assign ib_is_positive = ~signb_ipd | ~datab_ipd[datab_width-1];
 
    assign iabsa = ia_is_positive == 1 ? dataa_ipd[dataa_width-1:0] : -(dataa_ipd | (i_ones << dataa_width));
    assign iabsb = ib_is_positive == 1 ? datab_ipd[datab_width-1:0] : -(datab_ipd | (i_ones << datab_width));
 
    // multiply a * b
    assign iabsresult = iabsa * iabsb;
    assign dataout_tmp = (ia_is_positive ^ ib_is_positive) == 1 ? -iabsresult : iabsresult;
 
    // buf dataout_buf [dataout_width-1:0] (dataout, dataout_tmp);
    assign dataout = dataout_tmp;

endmodule

module cycloneiii_mac_mult	
   (
    dataa, 
    datab,
    signa, 
    signb,
    clk, 
    aclr, 
    ena,
    dataout,
    devclrn,
    devpor
    );
    
    parameter dataa_width    = 18;
    parameter datab_width    = 18;
    parameter dataa_clock	= "none";
    parameter datab_clock	= "none";
    parameter signa_clock	= "none"; 
    parameter signb_clock	= "none";
    parameter lpm_hint       = "true";
    parameter lpm_type       = "cycloneiii_mac_mult";
    
// SIMULATION_ONLY_PARAMETERS_BEGIN

    parameter dataout_width  = dataa_width + datab_width;

// SIMULATION_ONLY_PARAMETERS_END

    input [dataa_width-1:0] dataa;
    input [datab_width-1:0] datab;
    input 	signa;
    input 	signb;
    input clk;
    input aclr;
    input ena;
    input 	devclrn;
    input 	devpor;
 
    output [dataout_width-1:0] dataout;
    
    // tri1 devclrn;
    // tri1 devpor;

    wire [dataout_width-1:0] dataout_tmp; 
 
    wire [17:0] idataa_reg;	// optional register for dataa input
    wire [17:0] idatab_reg;	// optional register for datab input
    wire [17:0] dataa_pad;	// padded dataa input
    wire [17:0] datab_pad;	// padded datab input
    wire isigna_reg;			// optional register for signa input
    wire isignb_reg;			// optional register for signb input
    
    wire [17:0] idataa_int;	// dataa as seen by the multiplier input
    wire [17:0] idatab_int;	// datab as seen by the multiplier input
    wire isigna_int;			// signa as seen by the multiplier input
    wire isignb_int;			// signb as seen by the multiplier input
 
    wire ia_is_positive;
    wire ib_is_positive;
    wire [17:0] iabsa;		// absolute value (i.e. positive) form of dataa input
    wire [17:0] iabsb;		// absolute value (i.e. positive) form of datab input
    wire [35:0] iabsresult;	// absolute value (i.e. positive) form of product (a * b)
 
    wire dataa_use_reg;		// equivalent to dataa_clock parameter
    wire datab_use_reg;		// equivalent to datab_clock parameter
    wire signa_use_reg;		// equivalent to signa_clock parameter
    wire signb_use_reg;		// equivalent to signb_clock parameter
    
    reg [17:0] i_ones;		// padding with 1's for input negation

    wire reg_aclr;

    assign reg_aclr = (!devpor) || (!devclrn) || (aclr);

    // optional registering parameters
    assign dataa_use_reg = (dataa_clock != "none") ? 1'b1 : 1'b0;
    assign datab_use_reg = (datab_clock != "none") ? 1'b1 : 1'b0;
    assign signa_use_reg = (signa_clock != "none") ? 1'b1 : 1'b0;
    assign signb_use_reg = (signb_clock != "none") ? 1'b1 : 1'b0;
    assign dataa_pad = ((18-dataa_width) == 0) ? dataa : {{(18-dataa_width){1'b0}},dataa};
    assign datab_pad = ((18-datab_width) == 0) ? datab : {{(18-datab_width){1'b0}},datab};
       
    initial
    begin
        // 1's padding for 18-bit wide inputs
        i_ones = ~0;
    end
    
    // Optional input registers for dataa,b and signa,b
    cycloneiii_mac_data_reg dataa_reg (
                                      .clk(clk),
                                      .data(dataa_pad),
                                      .ena(ena),
                                      .aclr(reg_aclr),
                                      .dataout(idataa_reg)
                                     );
        defparam dataa_reg.data_width = dataa_width;

    cycloneiii_mac_data_reg datab_reg (
                                      .clk(clk),
                                      .data(datab_pad),
                                      .ena(ena),
                                      .aclr(reg_aclr),
                                      .dataout(idatab_reg)
                                     );
        defparam datab_reg.data_width = datab_width;

    cycloneiii_mac_sign_reg signa_reg (
                                      .clk(clk),
                                      .d(signa),
                                      .ena(ena),
                                      .aclr(reg_aclr),
                                      .q(isigna_reg)
                                     );

    cycloneiii_mac_sign_reg signb_reg (
                                      .clk(clk),
                                      .d(signb),
                                      .ena(ena),
                                      .aclr(reg_aclr),
                                      .q(isignb_reg)
                                     );

    // mux input sources from direct inputs or optional registers
    assign idataa_int = dataa_use_reg == 1'b1 ? idataa_reg : dataa;
    assign idatab_int = datab_use_reg == 1'b1 ? idatab_reg : datab;
    assign isigna_int = signa_use_reg == 1'b1 ? isigna_reg : signa;
    assign isignb_int = signb_use_reg == 1'b1 ? isignb_reg : signb;
 
    cycloneiii_mac_mult_internal mac_multiply (
                                              .dataa(idataa_int[dataa_width-1:0]),
                                              .datab(idatab_int[datab_width-1:0]),
                                              .signa(isigna_int), 
                                              .signb(isignb_int),
                                              .dataout(dataout)
                                             );
        defparam mac_multiply.dataa_width = dataa_width;
        defparam mac_multiply.datab_width = datab_width;
        defparam mac_multiply.dataout_width = dataout_width;

endmodule

module cycloneiii_mac_out	
   (
    dataa, 
    clk,
    aclr,
    ena,
    dataout,
    devclrn,
    devpor
    );
 
    parameter dataa_width   = 1;
    parameter output_clock  = "none";
    parameter lpm_hint      = "true";
    parameter lpm_type      = "cycloneiii_mac_out";

// SIMULATION_ONLY_PARAMETERS_BEGIN

    parameter dataout_width = dataa_width;

// SIMULATION_ONLY_PARAMETERS_END
    
    input [dataa_width-1:0] dataa;
    input clk;
    input aclr;
    input ena;
    input 	devclrn;
    input 	devpor;
    output [dataout_width-1:0] dataout; 
    
    // tri1 devclrn;
    // tri1 devpor;

    wire [dataa_width-1:0] dataa_ipd; // internal dataa
    wire clk_ipd; // internal clk
    wire aclr_ipd; // internal aclr
    wire ena_ipd; // internal ena
 
    // internal variable
    wire [dataout_width-1:0] dataout_tmp;

    reg [dataa_width-1:0] idataout_reg; // optional register for dataout output
 
    wire use_reg; // equivalent to dataout_clock parameter
    
    wire enable;
    wire no_aclr;

    // Input buffers
    buf (clk_ipd, clk);
    buf (aclr_ipd, aclr);
    buf (ena_ipd, ena);

    // buf dataa_buf [dataa_width-1:0] (dataa_ipd, dataa);
    assign dataa_ipd = dataa;

    // optional registering parameter
    assign use_reg = (output_clock != "none") ? 1 : 0;
    assign enable = (!aclr) && (ena) && use_reg;
    assign no_aclr = (!aclr) && use_reg;
       
    initial
    begin
       // initial values for optional register
       idataout_reg = 0;
    end
 
    // Optional input registers for dataa,b and signa,b
    always @* // (posedge clk_ipd or posedge aclr_ipd or negedge devclrn or negedge devpor)
    begin
       if (devclrn == 0 || devpor == 0 || aclr_ipd == 1)
       begin
          idataout_reg <= 0;
       end
       else if (ena_ipd == 1)
       begin
          idataout_reg <= dataa_ipd;
       end
    end
 
    // mux input sources from direct inputs or optional registers
    assign dataout_tmp = use_reg == 1 ? idataout_reg : dataa_ipd;
 
    // accelerate outputs
    // buf dataout_buf [dataout_width-1:0] (dataout, dataout_tmp);
    assign dataout = dataout_tmp;

endmodule
