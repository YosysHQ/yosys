#!/bin/bash

make -C ../..
set -x

vg=""
# vg="valgrind --leak-check=full --show-reachable=yes --log-file=valgrind.log"

cd aes_core
time $vg ../../../yosys -qt -l synth.log -o synth.v -s ../run-synth.ys \
	aes_cipher_top.v aes_inv_cipher_top.v aes_inv_sbox.v \
	aes_key_expand_128.v aes_rcon.v aes_sbox.v

cd ../fpu
time $vg ../../../yosys -qt -l synth.log -o synth.v -f "verilog -nolatches" -s ../run-synth.ys \
	fpu.v except.v post_norm.v pre_norm_fmul.v pre_norm.v primitives.v

cd ../i2c
time $vg ../../../yosys -qt -l synth.log -o synth.v -s ../run-synth.ys \
	i2c_master_top.v i2c_master_bit_ctrl.v i2c_master_byte_ctrl.v

cd ../sasc
time $vg ../../../yosys -qt -l synth.log -o synth.v -s ../run-synth.ys \
	sasc_top.v sasc_brg.v sasc_fifo4.v

cd ../simple_spi
time $vg ../../../yosys -qt -l synth.log -o synth.v -s ../run-synth.ys \
	simple_spi_top.v fifo4.v

cd ../spi
time $vg ../../../yosys -qt -l synth.log -o synth.v -s ../run-synth.ys \
	spi_top.v spi_clgen.v spi_shift.v

cd ../ss_pcm
time $vg ../../../yosys -qt -l synth.log -o synth.v -s ../run-synth.ys \
	pcm_slv_top.v

cd ../systemcaes
time $vg ../../../yosys -qt -l synth.log -o synth.v -s ../run-synth.ys \
	aes.v byte_mixcolum.v keysched.v mixcolum.v sbox.v subbytes.v word_mixcolum.v

cd ../usb_phy
time $vg ../../../yosys -qt -l synth.log -o synth.v -s ../run-synth.ys \
	usb_phy.v usb_rx_phy.v usb_tx_phy.v

