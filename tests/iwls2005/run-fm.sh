#!/bin/bash

if [ -n "$REMOTE_YOSYS_ROOT" ]; then
	rsync --exclude=".svn" --exclude="synth.log" --exclude="run-fm.sh" -rv -e "${REMOTE_YOSYS_SSH:-ssh}" "$REMOTE_YOSYS_ROOT"/tests/iwls2005/. .
fi

exec_fm()
{
	dir=$1; top=$2; shift; shift
	cat > $dir/fm.do <<- EOT
		set hdlin_ignore_full_case false
		set hdlin_warn_on_mismatch_message "FMR_ELAB-115 FMR_ELAB-146 FMR_ELAB-147"
		read_verilog -container r -libname WORK -01 { $* } 
		set_top r:/WORK/$top
		read_verilog -container i -libname WORK -01 synth.v
		# read_verilog -container i -technology_library -libname TECH_WORK -01 ../../../techlibs/stdcells_sim.v
		set_top i:/WORK/$top
		if ![verify] start_gui exit
	EOT
	( cd $dir; fm_shell -64 -file fm.do 2>&1 | tee fm.log; )
}

# cores that validated
exec_fm aes_core aes_cipher_top aes_cipher_top.v aes_inv_cipher_top.v aes_inv_sbox.v aes_key_expand_128.v aes_rcon.v aes_sbox.v
exec_fm i2c i2c_master_top i2c_master_top.v i2c_master_bit_ctrl.v i2c_master_byte_ctrl.v
exec_fm sasc sasc_top sasc_top.v sasc_brg.v sasc_fifo4.v
exec_fm simple_spi simple_spi_top simple_spi_top.v fifo4.v
exec_fm spi spi_top spi_top.v spi_clgen.v spi_shift.v
exec_fm ss_pcm pcm_slv_top pcm_slv_top.v
exec_fm systemcaes aes aes.v byte_mixcolum.v keysched.v mixcolum.v sbox.v subbytes.v word_mixcolum.v
exec_fm usb_phy usb_phy usb_phy.v usb_rx_phy.v usb_tx_phy.v

# cores with known problems (the fpu core unfortunately was designed with logic loops)
#exec_fm fpu fpu fpu.v except.v post_norm.v pre_norm_fmul.v pre_norm.v primitives.v

# summary
echo; echo
for x in */fm.log; do
	echo -e "${x%/*}\\t$( egrep '^Verification (SUCCEEDED|FAILED)' $x; )"
done | expand -t15
echo; echo

