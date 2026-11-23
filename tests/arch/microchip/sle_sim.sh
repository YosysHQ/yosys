set -e
iverilog -o test_sle sle_tb.v ../../../techlibs/microchip/cells_sim.v
vvp -N ./test_sle
