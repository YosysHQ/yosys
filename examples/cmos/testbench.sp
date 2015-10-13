
* supply voltages
.global Vss Vdd
Vss Vss 0 DC 0
Vdd Vdd 0 DC 3

* simple transistor model
.MODEL cmosn NMOS LEVEL=1 VT0=0.7 KP=110U GAMMA=0.4 LAMBDA=0.04 PHI=0.7
.MODEL cmosp PMOS LEVEL=1 VT0=-0.7 KP=50U GAMMA=0.57 LAMBDA=0.05 PHI=0.8

* load design and library
.include synth.sp
.include cmos_cells.sp

* input signals
Vclk clk 0 PULSE(0 3 1 0.1 0.1 0.8 2)
Vrst rst 0 PULSE(0 3 0.5 0.1 0.1 2.9 40)
Ven  en  0 PULSE(0 3 0.5 0.1 0.1 5.9 8)

Xuut clk rst en out0 out1 out2 COUNTER

.tran 0.01 50

.control
run
plot v(clk) v(rst)+5 v(en)+10 v(out0)+20 v(out1)+25 v(out2)+30
.endc

.end
