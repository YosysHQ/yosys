import_device eagle_s20.db -package BG256
read_verilog full.v -top demo
read_adc demo.adc
optimize_rtl
map_macro
map
pack
place
route
report_area -io_info -file demo_phy.area
bitgen -bit demo.bit -version 0X0000 -svf demo.svf -svf_comment_on -g ucode:00000000000000000000000000000000
