yosys -import
read_verilog clockgate.v
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
# Override only the in-memory small-cell models, not the shared Liberty file.
read_verilog -overwrite clockgate_icg.v
yosys proc
opt
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

#------------------------------------------------------------------------------

design -load before
clockgate -liberty clockgate.lib -dont_use pos_small -dont_use neg_small

# rising edge ICGs
select -module dffe_10 -assert-count 1 t:\\pos_big
select -module dffe_11 -assert-count 1 t:\\pos_big

# falling edge ICGs
select -module dffe_00 -assert-count 1 t:\\neg_big
select -module dffe_01 -assert-count 1 t:\\neg_big

#------------------------------------------------------------------------------

# SDFFE tests
foreach mod {sdffe_00 sdffe_01 sdffe_10 sdffe_11 sdffe_wide sdffe_separate_reset} {
    design -load before
    hierarchy -top $mod
    read_liberty -lib c*ckgate.lib
    equiv_opt -assert -map %map -multiclock clockgate -liberty c*ckgate.lib
    design -load postopt
    design -copy-to sdffe_final $mod
}

design -load sdffe_final

# falling-edge SDFFEs use neg_small, and rising-edge SDFFEs use pos_small for icg
select -module sdffe_00 -assert-count 1 t:neg_small
select -module sdffe_00 -assert-count 0 t:pos_small
select -module sdffe_01 -assert-count 1 t:neg_small
select -module sdffe_01 -assert-count 0 t:pos_small
select -module sdffe_10 -assert-count 1 t:pos_small
select -module sdffe_10 -assert-count 0 t:neg_small
select -module sdffe_11 -assert-count 1 t:pos_small
select -module sdffe_11 -assert-count 0 t:neg_small

# all kinds of sdffes keep reset and lose their individual enables
select -module sdffe_00 -assert-count 1 {t:$sdff}
select -module sdffe_00 -assert-count 0 {t:$sdffe}
select -module sdffe_01 -assert-count 1 {t:$sdff}
select -module sdffe_01 -assert-count 0 {t:$sdffe}
select -module sdffe_10 -assert-count 1 {t:$sdff}
select -module sdffe_10 -assert-count 0 {t:$sdffe}
select -module sdffe_11 -assert-count 1 {t:$sdff}
select -module sdffe_11 -assert-count 0 {t:$sdffe}

# the four-bit register needs one ICG and one vector SDFF
select -module sdffe_wide -assert-count 1 t:pos_small
select -module sdffe_wide -assert-count 0 t:neg_small
select -module sdffe_wide -assert-count 1 {t:$sdff}
select -module sdffe_wide -assert-count 0 {t:$sdffe}


# different reset signals must use differnt clock gate (2 pos_small)
select -module sdffe_separate_reset -assert-count 2 t:pos_small
select -module sdffe_separate_reset -assert-count 0 t:neg_small
select -module sdffe_separate_reset -assert-count 2 {t:$sdff}
select -module sdffe_separate_reset -assert-count 0 {t:$sdffe}
select -clear
