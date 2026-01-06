/********ADC***********/
//ADC for LRC,GW5AT-138K
module ADCLRC (
//Voltage signal source, /mV
  input  ADCINBK2A,       //input from bank2 IO, adc_in_b is the reference
  input  ADCINBK2B,       //input from bank2 IO, adc_in_b is the reference
  input  ADCINBK3A,       //input from bank3 IO, adc_in_b is the reference
  input  ADCINBK3B,       //input from bank3 IO, adc_in_b is the reference
  input  ADCINBK4A,       //input from bank4 IO, adc_in_b is the reference
  input  ADCINBK4B,       //input from bank4 IO, adc_in_b is the reference
  input  ADCINBK5A,       //input from bank5 IO, adc_in_b is the reference
  input  ADCINBK5B,       //input from bank5 IO, adc_in_b is the reference

//control signal
  input  [2:0] VSENCTL,    //Input source selection (ciu), from 0 to 7: adcv, adct, vdd09_0, vdd09_1, vdd18_0, vdd18_1, vdd33_0, vdd33_1

  input [9:0] FSCAL_VALUE,   // temperature mode 510~948, typical value 730; Voltage mode 452~840, typical value 653
  input [11:0] OFFSET_VALUE, //signed number, temperature mode - 1560~- 760, typical value - 1180; Voltage mode - 410~410, typical value 0

  input  ADCEN,         //Enable signal, active high
  input  CLK,           //clk input，1/2 shared
  input  DRSTN,         //0/1 shared, Digital part reset signal, active low
  input  ADCREQI,       //Measurement request signal, valid rising edge, asynchronous signal

  //output
  output ADCRDY,          //The measurement completion signal, active high
  output [13:0] ADCVALUE //The measurement result output, signed number. In voltage mode,/2048 is the actual measured value; In temperature mode,/4 is the actual measured value

);

  parameter DYN_BKEN = "FALSE";//"FALSE","TRUE"."TRUE",BUF_BK2_EN[0]&BUF_BK3_EN[0]=1
//Input source selection，1/2 shared
  parameter BUF_SERDES_Q1_EN = 3'b000;    //[1:0] does not support "11"
  parameter BUF_BK2_EN       = 6'b000000; //[3:0] Only one bit can be 1 at the same time
  parameter BUF_BK3_EN       = 6'b000000; //[3:0] Only one bit can be 1 at the same time
  parameter BUF_BK4_EN       = 6'b000000; //[3:0] Only one bit can be 1 at the same time
  parameter BUF_BK5_EN       = 6'b000000; //[3:0] Only one bit can be 1 at the same time
  parameter BUF_BK10_EN      = 5'b00000;  //[3:1] Only one bit can be 1 at the same time
  parameter BUF_BK11_EN      = 5'b00000;  //[3:1] Only one bit can be 1 at the same time
//Analog terminal option
  parameter CLK_SEL          = 1'b0;      //Clock source selection. 0,PIOCLK_SEL，1,ciu_clk
  parameter PIOCLK_SEL       = 1'b0;      //Clock source selection. 1/2 shared，0,mck_adc_clk_osc，1,io_clk
  parameter VSEN_CTL         = 3'b000;    //Input source selection
  parameter VSEN_CTL_SEL     = 1'b0;      //vsen_ctl source selection，0,VSEN_CTL，1,ciu_vsen_ctl
  parameter ADC_MODE      = 1'b0;      //Mode selection
  parameter DIV_CTL       = 2'd0;      //clock division，0:/1，1:/2，2:/4，3:/8，Clock after frequency division, 500kHz~8MHz

  //Digital terminal options
  parameter SAMPLE_CNT_SEL   = 3'd4;      //total samples configuration, 0~4:64, 128, 256, 512, 1024 sampling points, and the other values are 2048 sampling points.The total number of samples shall be greater than 7 * sampling period, i.e.  SAMPLR_CNT_SEL >= RATE_CHANGE_CTRL-1
  parameter RATE_CHANGE_CTRL = 3'd4;      //Sampling period configuration, 0~4:4、8、16、32、64，other values are 128


endmodule

//ADCULC,GW5AT-138K
module ADCULC (

  //Voltage signal source, /mV
  input  ADCINBK6A,       //input from bank6 IO, adc_in_b is the reference
  input  ADCINBK6B,       //input from bank6 IO, adc_in_b is the reference
  input  ADCINBK7A,       //input from bank7 IO, adc_in_b is the reference
  input  ADCINBK7B,       //input from bank7 IO, adc_in_b is the reference

  //control signal
  input  [2:0] VSENCTL,    //Input source selection(cib)，0~7: vtest, vdd09_0, vdd09_1, vdd09_2, vdd18_0, vdd18_1, reserved, vdd33

  input [9:0] FSCAL_VALUE,   // temperature mode 510~948, typical value 730; Voltage mode 452~840, typical value 653
  input [11:0] OFFSET_VALUE, //signed number, temperature mode - 1560~- 760, typical value - 1180; Voltage mode - 410~410, typical value 0

  input  ADCEN,         //Enable signal, active high
  input  CLK,           //clk input
  input  DRSTN,         //0/1 shared, Digital part reset signal, active low
  input   ADCREQI,      //Measurement request signal, valid rising edge, asynchronous signal
  output  ADCRDY,       //The measurement completion signal, active high
  output  [13:0] ADCVALUE //The measurement result output, signed number. In voltage mode,/2048 is the actual measured value; In temperature mode,/4 is the actual measured value

);
  parameter DYN_BKEN = "FALSE";//"FALSE","TRUE"."TRUE",BUF_BK6_EN[0]&BUF_BK7_EN[0]=1

//Input source selection
  parameter BUF_VCC_EN       = 1'b0;      //ulc
  parameter BUF_VCCM_EN      = 1'b0;      //ulc
  parameter BUF_MIPI_M0_EN   = 3'b000;    //ulc,[1:0] Only one bit can be 1 at the same time
  parameter BUF_MIPI_M1_EN   = 3'b000;    //ulc,[1:0] Only one bit can be 1 at the same time
  parameter BUF_SERDES_Q0_EN = 3'b000;    //ulc,[1:0] Only one bit can be 1 at the same time
  parameter BUF_BK6_EN       = 6'b000000; //bk6,[3:0] Only one bit can be 1 at the same time
  parameter BUF_BK7_EN       = 6'b000000; //bk7,[3:0] Only one bit can be 1 at the same time
//Analog terminal option
  parameter CLK_SEL          = 1'b0;      //Clock source selection. 0,PIOCLK_SEL，1,ciu_clk
  parameter PIOCLK_SEL       = 1'b0;      //Clock source selection. 1/2 shared，0,mck_adc_clk_osc，1,io_clk
  parameter VSEN_CTL         = 3'b000;    //Input source selection
  parameter VSEN_CTL_SEL     = 1'b0;      //vsen_ctl source selection，0,VSEN_CTL，1,ciu_vsen_ctl
  parameter ADC_MODE      = 1'b0;      //Mode selection
  parameter DIV_CTL          = 2'd0;      //clock division，0:/1，1:/2，2:/4，3:/8，Clock after frequency division, 500kHz~8MHz

//Digital terminal options
  parameter SAMPLE_CNT_SEL   = 3'd4;      //total samples configuration, 0~4:64, 128, 256, 512, 1024 sampling points, and the other values are 2048 sampling points.The total number of samples shall be greater than 7 * sampling period, i.e.  SAMPLR_CNT_SEL >= RATE_CHANGE_CTRL-1
  parameter RATE_CHANGE_CTRL = 3'd4;      //Sampling period configuration, 0~4:4、8、16、32、64，other values are 128

endmodule


//ADC,GW5A-25
module ADC (

  //control signal
  input  CLK,               //clk input
  input  [2:0] VSENCTL,     //Input source selection (ciu), from 0 to 7: glo_left,glo_right,loc_left,vtest,vcc_rt,vccc_rt,vccm_rt,vccx_buf
  input  ADCMODE,           //Mode selection,0:temperature mode，1:voltage mode
  input  DRSTN,             //Digital part reset signal, active low
  input  ADCREQI,           //Measurement request signal, valid rising edge, asynchronous signal
  output ADCRDY,          //The measurement completion signal, active high
  output [13:0] ADCVALUE, //The measurement result output, signed number. In voltage mode,/2048 is the actual measured value; In temperature mode,/4 is the actual measured value
  //mdrp
  input  MDRP_CLK,              //mdrp clock
  input  [7:0] MDRP_WDATA,      //mdrp write data
  input  MDRP_A_INC,            //mdrp self-increased address
  input  [1:0] MDRP_OPCODE,     //mdrp opcode
  output [7:0] MDRP_RDATA,       //mdrp read data
  input  ADCEN              //Enable signal, active high

);

  //Analog terminal option
  parameter CLK_SEL         = 1'b0;      //时钟源选择，0:osc(2.5MHz)，1:CLK
  parameter DIV_CTL         = 2'd0;      //clock division，0:/1，1:/2，2:/4，3:/8，Clock after frequency division, 500kHz~8MHz

  //Input source selection
  parameter BUF_EN          = 12'b000000000000; //
  parameter BUF_BK0_VREF_EN = 1'b0;  //
  parameter BUF_BK1_VREF_EN = 1'b0;  //
  parameter BUF_BK2_VREF_EN = 1'b0;  //
  parameter BUF_BK3_VREF_EN = 1'b0;  //
  parameter BUF_BK4_VREF_EN = 1'b0;  //
  parameter BUF_BK5_VREF_EN = 1'b0;  //
  parameter BUF_BK6_VREF_EN = 1'b0;  //
  parameter BUF_BK7_VREF_EN = 1'b0;  //

  //Digital terminal options
  parameter CSR_ADC_MODE      = 1'b1;       // Mode selection
  parameter CSR_VSEN_CTRL        = 3'd0;       // signal source:vccx/vccio_*/vcc_reg -> 7, signal source:vcc_ext -> 4, others -> 0
  parameter CSR_SAMPLE_CNT_SEL   = 3'd4;       // total samples configuration, 0~4:64, 128, 256, 512, 1024 sampling points, and the other values are 2048 sampling points.The total number of samples shall be greater than 7 * sampling period, i.e.  SAMPLR_CNT_SEL >= RATE_CHANGE_CTRL-1
  parameter CSR_RATE_CHANGE_CTRL = 3'd4;       // Sampling period configuration, 0~4:4、8、16、32、64，other values are 128
  parameter CSR_FSCAL            = 10'd730;    // Parameter 1: temperature mode 510~948, typical value 730; Voltage mode 452~840, typical value 653
  parameter CSR_OFFSET           = -12'd1180;  // Parameter 2, signed number, temperature mode - 1560~- 760, typical value - 1180; Voltage mode - 410~410, typical value 0


endmodule


//ADC_SAR,integrated saradc and adc functions.
module ADC_SAR (
//`ifdef ADC
  input  ADCMODE,          //Mode selection
  input  [2:0] VSENCTL,    //Input source selection
  input  CLK,              //clk input
  //Digital
  output ADCENO,           //Enable signal, active high
  input  DRSTN,            //Digital part reset signal, active low
  input  ADCREQI,          //Measurement request signal
  output ADCRDY,           //The measurement completion signal, active high
  output [13:0] ADCVALUE,  //The measurement result output
  input  MDRP_CLK,         //mdrp clock
  input  [7:0] MDRP_WDATA, //mdrp write data
  input  MDRP_A_INC,       //mdrp self-increased address
  input  [1:0] MDRP_OPCODE,//mdrp opcode
  output [7:0] MDRP_RDATA, //mdrp read data
  //Analog
  output ADC1BIT,          //Analog data output
  output ADCCLKO,          //Analog clock output
  input  ADCENI,           //fabric adc enable input
//`endif
// SAR
//`ifdef SARADC
  output [12:0] ADCBIT,    //Measurement result output
  output CLKO,             //output clk
  output EOC,              //The measurement completion signal
  input  CLKI,             //fabric input clk
  input  [6:0] CHEN,       //channel select
  input  RSTN,             //resetn,active low
  input  SOC              //Measurement request signal
//`endif
);

  parameter BUF_EN = 29'b0;    // signal source selecor switch
// Δ-Σ
//`ifdef ADC
  parameter CLK_SEL        = 1'b1;     // clk source select
  parameter DIV_CTL        = 2'd0;     // clock division.0:/1,1:/2,2:/4,3:/8
  parameter ADC_EN_SEL     = 1'b0;     // adc_en source select
  parameter PHASE_SEL      = 1'b0;     // adc internal data phase select

  //Digital terminal options
  parameter CSR_ADC_MODE         = 1'b1;          // Mode selection
  parameter CSR_VSEN_CTRL        = 3'd0;       // signal source:vccx/vccio_*/vcc_reg -> 7, signal source:vcc_ext -> 4, others -> 0
  parameter CSR_SAMPLE_CNT_SEL   = 3'd4;       // total samples configuration, 0~4:64, 128, 256, 512, 1024 sampling points, and the other values are 2048 sampling points.The total number of samples shall be greater than 7 * sampling period, i.e.  SAMPLR_CNT_SEL >= RATE_CHANGE_CTRL-1
  parameter CSR_RATE_CHANGE_CTRL = 3'd4;       // Sampling period configuration, 0~4:4、8、16、32、64，other values are 128
  parameter CSR_FSCAL            = 10'd730;    // Parameter 1: temperature mode 510~948, typical value 730; Voltage mode 452~840, typical value 653
  parameter CSR_OFFSET           = -12'd1180;  // Parameter 2, signed number, temperature mode - 1560~- 760, typical value - 1180; Voltage mode - 410~410, typical value 0

//`endif
// SAR
//`ifdef SARADC
  parameter ADC_CLK_DIV        = 2'b00;     // clock division.00:/1,01:/2,10:/4,11:/8
  parameter ADC_CLKDIV_EN      = 1'b0;     // clock division enable
  parameter CLK_SRC_SEL        = 1'b1;     // source clock sel
  parameter VREF_BUF_EN        = 1'b1;     // BGR vref buffer enable
  parameter COUNT_LEN          = 5'b10100; // ADC counter length
  parameter DAC_SAMPLE_END     = 5'b10010; // DAC sample end point
  parameter DAC_SAMPLE_START   = 5'b01101; // DAC sample start point
  parameter SH_SAMPLE_END      = 5'b01011; // SH sample start point
  parameter SH_SAMPLE_START    = 5'b00001; // SH sample end point
  parameter AUTO_CHOP_EN       = 1'b0;     // auto chop
  parameter CHOP_CLK_DIV       = 4'b0;     // chop clock divider

//`endif

endmodule


//ADCA,15k
module ADCA (
// analog
  input  ADCMODE,          //Mode selection
  input  [2:0] VSENCTL,    //Input source selection 0-7: vglo_left, vglo_right, vcc2, vccc3, vccb4, vcc5, vccm6, vccc7
  input  CLK,              //clk input
  input  ADCENI,           //fabric adc enable input
  input  PWRON_DYN,        //power enable. 1:on 0:off
  // digital
  input  DRSTN,            //Digital part reset signal, active low
  input  ADCREQI,          //Measurement request signal
  output ADCRDY,           //The measurement completion signal, active high
  output [13:0] ADCVALUE,  //The measurement result output
  input  MDRP_CLK,         //mdrp clock
  input  [7:0] MDRP_WDATA, //mdrp write data
  input  MDRP_A_INC,       //mdrp self-increased address
  input  [1:0] MDRP_OPCODE,//mdrp opcode
  output [7:0] MDRP_RDATA  //mdrp read data
);

  parameter BUF_EN = 20'b0;    // signal source selecor switch //[8:0] one-hot; [19:15] one-hot. BUF_EN[6] must be 0
  parameter CLK_SEL        = 1'b1;     // clk source select
  parameter DIV_CTL        = 2'd0;     // clock division
  parameter ADC_EN_SEL     = 1'b0;     // adc_en source select
  parameter PHASE_SEL      = 1'b0;     // adc internal data phase select

  parameter PWRON_SEL      = 1'b0;     // power enbale source select. 0:PWRON 1:PWRON_DYN
  parameter PWRON          = 1'b1;     // as PWRON_DYN
  parameter LDO_MODE       = 1'b0;     // LDO mode 0:on(2.5/3.3V) 1:off(1.8V)

  //Digital terminal options
  parameter CSR_ADC_MODE         = 1'b1;       // Mode selection
  parameter CSR_VSEN_CTRL        = 3'd0;       // signal source:vccx/vccio_*/vcc_reg -> 7, signal source:vcc_ext -> 4, others -> 0
  parameter CSR_SAMPLE_CNT_SEL   = 3'd4;       // total samples configuration, 0~4:64, 128, 256, 512, 1024 sampling points, and the other values are 2048 sampling points.The total number of samples shall be greater than 7 * sampling period, i.e.  SAMPLR_CNT_SEL >= RATE_CHANGE_CTRL-1
  parameter CSR_RATE_CHANGE_CTRL = 3'd4;       // Sampling period configuration, 0~4:4、8、16、32、64，other values are 128
  parameter CSR_FSCAL            = 10'd730;    // Parameter 1: temperature mode 510~948, typical value 730; Voltage mode 452~840, typical value 653
  parameter CSR_OFFSET           = -12'd1180;  // Parameter 2, signed number, temperature mode - 1560~- 760, typical value - 1180; Voltage mode - 410~410, typical value 0

endmodule

