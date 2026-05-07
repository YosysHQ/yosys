yosys -import
read_verilog clockgate.v
read_verilog ../sim/sdffe.v
yosys proc
opt

design -save before

#------------------------------------------------------------------------------

# Test -pos

clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen

# falling edge clock flops don't get matched on -pos
select -module dffe_00 -assert-count 0 t:\\pdk_icg
select -module dffe_01 -assert-count 0 t:\\pdk_icg
# rising edge clock flops do get matched on -pos
select -module dffe_10 -assert-count 1 t:\\pdk_icg
select -module dffe_11 -assert-count 1 t:\\pdk_icg
# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_10 -assert-count 1 t:\$_NOT_
select -module dffe_11 -assert-count 0 t:\$_NOT_

# Extra credit: multi-bit FFs work fine as well
select -module dffe_wide_11 -assert-count 1 t:\\pdk_icg

#------------------------------------------------------------------------------

# Test -neg

design -load before
clockgate -min_net_size 1 -neg pdk_icg ce:clkin:clkout -tie_lo scanen

# falling edge clock flops do get matched on -neg
select -module dffe_00 -assert-count 1 t:\\pdk_icg
select -module dffe_01 -assert-count 1 t:\\pdk_icg
# rising edge clock flops don't get matched on -neg
select -module dffe_10 -assert-count 0 t:\\pdk_icg
select -module dffe_11 -assert-count 0 t:\\pdk_icg
# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_00 -assert-count 1 t:\$_NOT_
select -module dffe_01 -assert-count 0 t:\$_NOT_

#------------------------------------------------------------------------------

# Same as first case, but on fine-grained cells

design -load before

techmap

clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen

# falling edge clock flops don't get matched on -pos
select -module dffe_00 -assert-count 0 t:\\pdk_icg
select -module dffe_01 -assert-count 0 t:\\pdk_icg
# falling edge clock flops do get matched on -pos
select -module dffe_10 -assert-count 1 t:\\pdk_icg
select -module dffe_11 -assert-count 1 t:\\pdk_icg
# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_10 -assert-count 1 t:\$_NOT_
select -module dffe_11 -assert-count 0 t:\$_NOT_

# Extra credit: multi-bit FFs work fine as well
select -module dffe_wide_11 -assert-count 1 t:\\pdk_icg

#------------------------------------------------------------------------------

design -load before
clockgate -min_net_size 2 -neg pdk_icg ce:clkin:clkout -tie_lo scanen

# No FF set sharing a (clock, clock enable) pair is large enough
select -module dffe_00 -assert-count 0 t:\\pdk_icg
select -module dffe_01 -assert-count 0 t:\\pdk_icg
select -module dffe_10 -assert-count 0 t:\\pdk_icg
select -module dffe_11 -assert-count 0 t:\\pdk_icg

#------------------------------------------------------------------------------

design -reset
read_rtlil clockgate_bad.il

# Check we don't choke on constants
clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -module bad1 -assert-count 0 t:\\pdk_icg
select -module bad2 -assert-count 0 t:\\pdk_icg

#------------------------------------------------------------------------------

# Regression test: EN is a bit from a multi-bit wire
design -reset
read_verilog clockgate_wide.v
yosys proc
opt

clockgate -pos pdk_icg ce:clkin:clkout -tie_lo scanen
select -assert-count 1 t:\\pdk_icg

#------------------------------------------------------------------------------

design -reset
read_liberty c*ckgate.lib
design -save map
foreach mod {dffe_00 dffe_01 dffe_10 dffe_11} {
    design -load before
    hierarchy -top $mod
    read_liberty -lib c*ckgate.lib
    equiv_opt -map %map -multiclock clockgate -liberty c*ckgate.lib
    design -load postopt
    design -copy-to final $mod
}
design -load final

# rising edge ICGs
select -module dffe_00 -assert-count 0 t:\\pos_small
select -module dffe_01 -assert-count 0 t:\\pos_small

select -module dffe_10 -assert-count 1 t:\\pos_small
select -module dffe_11 -assert-count 1 t:\\pos_small

# falling edge ICGs
select -module dffe_00 -assert-count 1 t:\\neg_small
select -module dffe_01 -assert-count 1 t:\\neg_small

select -module dffe_10 -assert-count 0 t:\\neg_small
select -module dffe_11 -assert-count 0 t:\\neg_small

# and nothing else
select -module dffe_00 -assert-count 0 t:\\pos_big
select -module dffe_01 -assert-count 0 t:\\pos_big
select -module dffe_10 -assert-count 0 t:\\pos_big
select -module dffe_11 -assert-count 0 t:\\pos_big
select -module dffe_00 -assert-count 0 t:\\pos_small_tielo
select -module dffe_01 -assert-count 0 t:\\pos_small_tielo
select -module dffe_10 -assert-count 0 t:\\pos_small_tielo
select -module dffe_11 -assert-count 0 t:\\pos_small_tielo
select -module dffe_00 -assert-count 0 t:\\neg_big
select -module dffe_01 -assert-count 0 t:\\neg_big
select -module dffe_10 -assert-count 0 t:\\neg_big
select -module dffe_11 -assert-count 0 t:\\neg_big
select -module dffe_00 -assert-count 0 t:\\neg_small_tielo
select -module dffe_01 -assert-count 0 t:\\neg_small_tielo
select -module dffe_10 -assert-count 0 t:\\neg_small_tielo
select -module dffe_11 -assert-count 0 t:\\neg_small_tielo

# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_10 -assert-count 1 t:\$_NOT_
select -module dffe_11 -assert-count 0 t:\$_NOT_

#------------------------------------------------------------------------------

# test multiple liberty files to behave the same way
design -load before
clockgate -liberty clockgate_pos.lib -liberty clockgate_neg.lib

# rising edge ICGs
select -module dffe_00 -assert-count 0 t:\\pos_small
select -module dffe_01 -assert-count 0 t:\\pos_small

select -module dffe_10 -assert-count 1 t:\\pos_small
select -module dffe_11 -assert-count 1 t:\\pos_small

# falling edge ICGs
select -module dffe_00 -assert-count 1 t:\\neg_small
select -module dffe_01 -assert-count 1 t:\\neg_small

select -module dffe_10 -assert-count 0 t:\\neg_small
select -module dffe_11 -assert-count 0 t:\\neg_small

# and nothing else
select -module dffe_00 -assert-count 0 t:\\pos_big
select -module dffe_01 -assert-count 0 t:\\pos_big
select -module dffe_10 -assert-count 0 t:\\pos_big
select -module dffe_11 -assert-count 0 t:\\pos_big
select -module dffe_00 -assert-count 0 t:\\pos_small_tielo
select -module dffe_01 -assert-count 0 t:\\pos_small_tielo
select -module dffe_10 -assert-count 0 t:\\pos_small_tielo
select -module dffe_11 -assert-count 0 t:\\pos_small_tielo
select -module dffe_00 -assert-count 0 t:\\neg_big
select -module dffe_01 -assert-count 0 t:\\neg_big
select -module dffe_10 -assert-count 0 t:\\neg_big
select -module dffe_11 -assert-count 0 t:\\neg_big
select -module dffe_00 -assert-count 0 t:\\neg_small_tielo
select -module dffe_01 -assert-count 0 t:\\neg_small_tielo
select -module dffe_10 -assert-count 0 t:\\neg_small_tielo
select -module dffe_11 -assert-count 0 t:\\neg_small_tielo

# if necessary, EN is inverted, since the given ICG
# is assumed to have an active-high EN
select -module dffe_10 -assert-count 1 t:\$_NOT_
select -module dffe_11 -assert-count 0 t:\$_NOT_

# $sdffe is not gated
select -module sdffe -assert-count 0 sdffe t:* t:\$sdffe %d

#------------------------------------------------------------------------------

design -load before
clockgate -liberty clockgate.lib -dont_use pos_small -dont_use neg_small

# rising edge ICGs
select -module dffe_10 -assert-count 1 t:\\pos_big
select -module dffe_11 -assert-count 1 t:\\pos_big

# falling edge ICGs
select -module dffe_00 -assert-count 1 t:\\neg_big
select -module dffe_01 -assert-count 1 t:\\neg_big
