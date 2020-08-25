PROJECT(passes)

SET(PASSES_FSM_SRC
        fsm/fsmdata.h
        fsm/fsm_map.cc
        fsm/fsm_info.cc
        fsm/fsm_recode.cc
        fsm/fsm_extract.cc
        fsm/fsm_opt.cc
        fsm/fsm_export.cc
        fsm/fsm_expand.cc
        fsm/fsm.cc
        fsm/fsm_detect.cc
        )

SET(PASSES_CMDS_SRC
        cmds/logcmd.cc
        cmds/setundef.cc
        cmds/cover.cc
        cmds/logger.cc
        cmds/splice.cc
        cmds/check.cc
        cmds/torder.cc
        cmds/plugin.cc
        cmds/stat.cc
        cmds/show.cc
        cmds/tee.cc
        cmds/select.cc
        cmds/bugpoint.cc
        cmds/setattr.cc
        cmds/blackbox.cc
        cmds/delete.cc
        cmds/scatter.cc
        cmds/write_file.cc
        cmds/copy.cc
        cmds/portlist.cc
        cmds/add.cc
        cmds/printattrs.cc
        cmds/rename.cc
        cmds/connect.cc
        cmds/design.cc
        cmds/exec.cc
        cmds/trace.cc
        cmds/qwp.cc
        cmds/connwrappers.cc
        cmds/autoname.cc
        cmds/splitnets.cc
        cmds/edgetypes.cc
        cmds/ltp.cc
        cmds/chtype.cc
        cmds/scc.cc
        cmds/chformal.cc
        cmds/scratchpad.cc
        )

SET(PASSES_OPT_SRC
        opt/opt_lut.cc
        opt/opt_dff.cc
        opt/opt_share.cc
        opt/wreduce.cc
        opt/opt_muxtree.cc
        opt/opt_lut_ins.cc
        opt/pmux2shiftx.cc
        opt/share.cc
        opt/opt_reduce.cc
        opt/opt_expr.cc
        opt/rmports.cc
        opt/opt_merge.cc
        opt/opt_mem.cc
        opt/muxpack.cc
        opt/opt.cc
        opt/opt_rmdff.cc
        opt/opt_clean.cc
        opt/opt_demorgan.cc
        )

SET(PASSES_MEMORY_SRC
        memory/memory_bram.cc
        memory/memory_share.cc
        memory/memory_collect.cc
        memory/memory_map.cc
        memory/memory.cc
        memory/memory_unpack.cc
        memory/memory_nordff.cc
        memory/memory_dff.cc
        memory/memory_memx.cc
        )

SET(PASSES_PMGEN_SRC
        pmgen/generate.h
        pmgen/xilinx_dsp.cc
        pmgen/peepopt.cc
        pmgen/xilinx_srl.cc
        pmgen/ice40_wrapcarry.cc
        pmgen/test_pmgen.cc
        pmgen/ice40_dsp.cc
        )

SET(PASSES_TECHMAP_SRC
        techmap/simplemap.h
        techmap/libparse.h
        techmap/attrmap.cc
        techmap/muxcover.cc
        techmap/abc9.cc
        techmap/maccmap.cc
        techmap/aigmap.cc
        techmap/nlutmap.cc
        techmap/dff2dffs.cc
        techmap/pmuxtree.cc
        techmap/dfflegalize.cc
        techmap/libparse.cc
        techmap/abc9_ops.cc
        techmap/hilomap.cc
        techmap/extract_reduce.cc
        techmap/deminout.cc
        techmap/filterlib.cc
        techmap/abc.cc
        techmap/attrmvcp.cc
        techmap/lut2mux.cc
        techmap/insbuf.cc
        techmap/flowmap.cc
        techmap/zinit.cc
        techmap/clkbufmap.cc
        techmap/iopadmap.cc
        techmap/dffinit.cc
        techmap/dff2dffe.cc
        techmap/techmap.cc
        techmap/dfflibmap.cc
        techmap/abc9_exe.cc
        techmap/shregmap.cc
        techmap/extract_fa.cc
        techmap/extract_counter.cc
        techmap/simplemap.cc
        techmap/alumacc.cc
        techmap/flatten.cc
        techmap/extract.cc
        techmap/extractinv.cc
        techmap/dffunmap.cc
        techmap/tribuf.cc
        )

SET(PASSES_HIERARCHY_SRC
        hierarchy/submod.cc
        hierarchy/hierarchy.cc
        hierarchy/uniquify.cc
        )

SET(PASSES_TESTS_SRC
        tests/test_abcloop.cc
        tests/test_autotb.cc
        tests/test_cell.cc
        )

SET(PASSES_PROC_SRC
        proc/proc_dlatch.cc
        proc/proc_mux.cc
        proc/proc_init.cc
        proc/proc_rmdead.cc
        proc/proc.cc
        proc/proc_prune.cc
        proc/proc_clean.cc
        proc/proc_arst.cc
        proc/proc_dff.cc
        )

SET(PASSES_SAT_SRC
        sat/qbfsat.h
        sat/assertpmux.cc
        sat/supercover.cc
        sat/fmcombine.cc
        sat/freduce.cc
        sat/cutpoint.cc
        sat/sim.cc
        sat/fminit.cc
        sat/miter.cc
        sat/clk2fflogic.cc
        sat/qbfsat.cc
        sat/async2sync.cc
        sat/mutate.cc
        sat/eval.cc
        sat/sat.cc
        sat/expose.cc
        )

SET(PASSES_EQUIV_SRC
        equiv/equiv_miter.cc
        equiv/equiv_mark.cc
        equiv/equiv_induct.cc
        equiv/equiv_struct.cc
        equiv/equiv_remove.cc
        equiv/equiv_opt.cc
        equiv/equiv_simple.cc
        equiv/equiv_add.cc
        equiv/equiv_make.cc
        equiv/equiv_status.cc
        equiv/equiv_purge.cc
        )

SET(PASSES_SRC )
SET(ENABLED_PASSES )

MACRO(ADD_YOSYS_PASSES Name Enabled)
    OPTION(ENABLE_${Name}_PASS "Enable ${Name} pass." ${Enabled})
    IF (ENABLE_${Name}_PASS)
        SET(PASSES_SRC
                ${PASSES_SRC}
                ${PASSES_${Name}_SRC}
                )
        LIST(APPEND ENABLED_PASSES ${Name})
    ENDIF()
ENDMACRO()

ADD_YOSYS_PASSES(CMDS      ON)
ADD_YOSYS_PASSES(EQUIV     OFF)
ADD_YOSYS_PASSES(FSM       ON)
ADD_YOSYS_PASSES(HIERARCHY ON)
ADD_YOSYS_PASSES(MEMORY    ON)
ADD_YOSYS_PASSES(OPT       ON)
ADD_YOSYS_PASSES(PMGEN     OFF)
ADD_YOSYS_PASSES(PROC      ON)
ADD_YOSYS_PASSES(SAT       OFF)
ADD_YOSYS_PASSES(TECHMAP   OFF)
ADD_YOSYS_PASSES(TESTS     OFF)

MESSAGE("<< Enabled passes: ${ENABLED_PASSES} >>")
ADD_LIBRARY(${PROJECT_NAME} ${PASSES_SRC})
