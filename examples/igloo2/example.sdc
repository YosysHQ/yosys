# Add timing constraints here
create_clock -period 10.000 -waveform {0.000 5.000} [get_ports {clk}]
