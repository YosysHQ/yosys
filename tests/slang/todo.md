# Slang Flags

## Formal

Probably want to add a --formal flag, what is an example of a module that read_verilog handles differently with/without --formal

## Specify

what does the -specify flag on read_verilog do?

## Other

-noblackbox
-nomem2reg

# $initstate

This behavior should probably be fixed?

```systemverilog
`ifdef READ_SLANG
    reg initial_state = 1'b1;

    always @(posedge clock)
        initial_state <= 1'b0;

    always @*
        assume (reset == initial_state);
`elsif YOSYS
    always @*
        assume (reset == $initstate);
`endif
```

# Interesting Tests

tests/various/rand_const.ys
  - at least make it known that rand isn't supported anymore
tests/various/chparam.sh
  - IDK if this has an easy fix, I remember that slang has weird behavior with parameters but it should be documented at least

## TBD

./arith_tree/arith_tree_sub_chains.ys.err
./arith_tree/arith_tree_link_shape.ys.err
./sat/sizebits.ys.err
./sat/fminit_seq_width.ys.err
./sat/initval.ys.err
./sat/asserts_seq.ys.err
./verilog/param_default.ys.err
./verilog/typedef_across_files.ys.err
./verilog/param_no_default_unbound_5.ys.err
./verilog/func_arg_mismatch_3.ys.err
./verilog/func_arg_mismatch_4.ys.err
./verilog/asgn_expr_not_proc_3.ys.err
./verilog/macro_unapplied.ys.err
./verilog/parameters_across_files.ys.err
./verilog/package_end_label.ys.err
./verilog/constparser_f_file.ys.err
./verilog/block_end_label_wrong.ys.err
./verilog/func_task_arg_copying.ys.err
./verilog/always_comb_latch_1.ys.err
./verilog/param_no_default_unbound_1.ys.err
./verilog/asgn_expr_not_proc_2.ys.err
./verilog/sbvector.ys.err
./verilog/ifdef_unterminated.ys.err
./verilog/unmatched_endif_2.ys.err
./verilog/param_no_default_not_svmode.ys.err
./verilog/task_attr.ys.err
./verilog/genblk_port_decl.ys.err
./verilog/absurd_width.ys.err
./verilog/absurd_width_const.ys.err
./verilog/unique_priority_if.ys.err
./verilog/asgn_expr_not_proc_1.ys.err
./verilog/roundtrip_proc.ys.err
./verilog/genfor_decl_no_sv.ys.err
./verilog/func_arg_mismatch_1.ys.err
./verilog/localparam_no_default_1.ys.err
./verilog/delay_time_scale.ys.err
./verilog/macro_arg_tromp.ys.err
./verilog/conflict_assert.ys.err
./verilog/asgn_expr_not_proc_5.ys.err
./verilog/always_comb_latch_3.ys.err
./verilog/bug2042-sv.ys.err
./verilog/asgn_expr_not_proc_4.ys.err
./verilog/asgn_expr_not_sv_3.ys.err
./verilog/always_comb_latch_4.ys.err
./verilog/unmatched_elsif.ys.err
./verilog/asgn_expr_not_sv_1.ys.err
./verilog/for_decl_no_sv.ys.err
./verilog/param_no_default_unbound_2.ys.err
./verilog/gen_block_end_label_wrong.ys.err
./verilog/hidden_decl.ys.err
./verilog/unnamed_block.ys.err
./verilog/macro_unapplied_newline.ys.err
./verilog/gen_block_end_label_only.ys.err
./verilog/unique_if_else.ys.err
./verilog/genblk_wire.ys.err
./verilog/reset_auto_counter.ys.err
./verilog/asgn_expr_not_sv_2.ys.err
./verilog/unmatched_else.ys.err
./verilog/issue4402.ys.err
./verilog/global_parameter.ys.err
./verilog/for_decl_shadow.ys.err
./verilog/block_labels.ys.err
./verilog/specify-ifnone.ys.err
./verilog/mem_bounds.ys.err
./verilog/localparam_no_default_2.ys.err
./verilog/delay_risefall.ys.err
./verilog/conflict_cell_memory.ys.err
./verilog/param_no_default_unbound_3.ys.err
./verilog/conflict_wire_memory.ys.err
./verilog/bug2042.ys.err
./verilog/for_decl_no_init.ys.err
./verilog/delay_mintypmax.ys.err
./verilog/package_import_separate.ys.err
./verilog/conflict_memory_wire.ys.err
./verilog/param_no_default_unbound_4.ys.err
./verilog/func_arg_mismatch_2.ys.err
./verilog/unmatched_endif.ys.err
./verilog/constparser_f.ys.err
./verilog/always_comb_latch_2.ys.err
./verilog/void_func.ys.err
./verilog/module_end_label.ys.err
./verilog/const_sr.ys.err
./verilog/issue5745.ys.err
./verilog/package_import_specific.ys.err
./verilog/bug2493.ys.err
./verilog/string-literals.ys.err
./verilog/fcall_smoke.ys.err
./verilog/wire_and_var.ys.err
./verilog/genfor_decl_no_init.ys.err
./verilog/constparser_g.ys.err
./verilog/typedef_legacy_conflict.ys.err
./verilog/conflict_interface_port.ys.err
./verilog/genvar_loop_decl_1.ys.err
./verilog/block_end_label_only.ys.err
./verilog/bug4785.ys.err
./verilog/unbased_unsized_tern.ys.err
./verilog/asgn_expr_not_sv_4.ys.err
./blif/bug2729.ys.err
./arch/analogdevices/dsp_abc9.ys.err
./arch/analogdevices/bug1480.ys.err
./arch/analogdevices/bug1462.ys.err
./arch/analogdevices/bug1460.ys.err
./arch/fabulous/customisation.ys.err
./arch/quicklogic/qlf_k6n10f/dsp.ys.err
./arch/quicklogic/qlf_k6n10f/meminit.ys.err
./arch/nanoxplore/meminit.ys.err
./arch/nanoxplore/lutram.ys.err
./arch/xilinx/xilinx_srl_enable.ys.err
./arch/xilinx/dsp_abc9.ys.err
./arch/xilinx/abc9_dff.ys.err
./arch/xilinx/bug1480.ys.err
./arch/xilinx/dsp_cascade.ys.err
./arch/xilinx/xilinx_dsp.ys.err
./arch/xilinx/bug1462.ys.err
./arch/xilinx/dynamic_upto_select.ys.err
./arch/xilinx/bug1605.ys.err
./arch/xilinx/bug1460.ys.err
./arch/xilinx/xilinx_dffopt.ys.err
./arch/ice40/ice40_wrapcarry.ys.err
./arch/ice40/ice40_dsp_const.ys.err
./arch/ice40/ice40_dsp.ys.err
./arch/ice40/bug1597.ys.err
./arch/ice40/ice40_opt.ys.err
./arch/ecp5/abc9_inout_pad_input.ys.err
./arch/ecp5/bug2409.ys.err
./arch/ecp5/bug1459.ys.err
./alumacc/cmp_merge.ys.err
./abc_new/partial_box_ports.ys.err
./abc_new/scopeinfo.ys.err
./abc_new/mixed_cells_normal_lib.ys.err
./abc_new/bug5445.ys.err
./abc_new/paramod_equiv.ys.err
./abc_new/openroad/cm_cases.ys.err
./abc_new/openroad/liberty_boxes_empty.ys.err
./abc_new/openroad/remap_netlist.ys.err
./abc_new/openroad/tie_box.ys.err
./abc_new/openroad/liberty_boxes.ys.err
./abc_new/openroad/dffrsn_equiv.ys.err
./abc_new/selection.ys.err
./peepopt/muldiv_c.ys.err
./proc/bug2619.ys.err
./proc/yosys_latch.ys.err
./proc/proc_rom.ys.err
./proc/proc_latches.ys.err
./proc/bug2656.ys.err
./proc/bug6243.ys.err
./techmap/dfflibmap_proc_formal.ys.err
./techmap/wireinit.ys.err
./techmap/techmap_chtype.ys.err
./techmap/cellname.ys.err
./techmap/iopadmap.ys.err
./techmap/clkbufmap.ys.err
./techmap/module_not_derived.ys.err
./techmap/cmp2lcu.ys.err
./techmap/dfflibmap_formal.ys.err
./techmap/techmap_replace.ys.err
./techmap/cellmatch.ys.err
./techmap/dlatchlibmap_proc_formal.ys.err
./techmap/autopurge.ys.err
./techmap/bug2183.ys.err
./techmap/dffinit.ys.err
./techmap/bug2321.ys.err
./techmap/dlatchlibmap_formal.ys.err
./techmap/extractinv.ys.err
./opt/opt_share_bug2538.ys.err
./opt/memory_dff_trans.ys.err
./opt/opt_clean_init.ys.err
./opt/opt_expr_shr_int_max.ys.err
./opt/opt_expr_alu.ys.err
./opt/opt_dff-simplify.ys.err
./opt/opt_share_bug2335.ys.err
./opt/bug1793.ys.err
./opt/opt_pow.ys.err
./opt/opt_merge_properties.ys.err
./opt/bug5398.ys.err
./opt/opt_dff_sat_const.ys.err
./opt/pow_assoc.ys.err
./opt/bug1525.ys.err
./opt/opt_dff_eqbits.ys.err
./opt/opt_balance_tree.ys.err
./opt/memory_map_offset.ys.err
./opt/opt_expr.ys.err
./opt/bug3117.ys.err
./opt/opt_clean_mem.ys.err
./opt/opt_expr_more.ys.err
./opt/opt_expr_combined_assign.ys.err
./opt/bug2766.ys.err
./opt/opt_mem_feedback.ys.err
./opt/opt_expr_shift.ys.err
./opt/bug2765.ys.err
./opt/opt_expr_consumex.ys.err
./opt/opt_dff_dffmux.ys.err
