
* load design and library
.include cmos_cells_digital.sp
.include synth.sp

* input signals
Vclk clk 0 PULSE(0 3 1 0.1 0.1 0.8 2)
Vrst rst 0 PULSE(0 3 0.5 0.1 0.1 2.9 40)
Ven  en  0 PULSE(0 3 0.5 0.1 0.1 5.9 8)

Xuut dclk drst den dout0 dout1 dout2 counter
* Bridge to digital
.model adc_buff adc_bridge(in_low = 0.8 in_high=2)
.model dac_buff dac_bridge(out_high = 3.5)
Aad [clk rst en] [dclk drst den] adc_buff
Ada [dout0 dout1 dout2] [out0 out1 out2] dac_buff


.tran 0.01 50

.control
run
plot v(clk) v(rst)+5 v(en)+10 v(out0)+20 v(out1)+25 v(out2)+30
.endc

.end
