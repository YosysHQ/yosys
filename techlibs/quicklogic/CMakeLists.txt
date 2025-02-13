add_library(yosys_techlibs_quicklogic INTERFACE)

function(pmgen_command  _name)
    add_custom_command(
        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${_name}_pm.h
        COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/passes/pmgen/pmgen.py -o ${CMAKE_CURRENT_BINARY_DIR}/${_name}_pm.h -p ${_name} ${CMAKE_CURRENT_SOURCE_DIR}/${_name}.pmg
        DEPENDS ${CMAKE_SOURCE_DIR}/passes/pmgen/pmgen.py ${CMAKE_CURRENT_SOURCE_DIR}/${_name}.pmg
        COMMENT "Generating passes/pmgen/${_name}_pm.h..."
    )
endfunction()

pmgen_command(ql_dsp_macc)

target_sources(yosys_techlibs_quicklogic INTERFACE
    synth_quicklogic.cc
    ql_bram_merge.cc
    ql_bram_types.cc
    ql_dsp_simd.cc
    ql_dsp_io_regs.cc
    ql_dsp_macc.cc
)

target_sources(yosys_techlibs_quicklogic PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/ql_dsp_macc_pm.h)

target_link_libraries(yosys PRIVATE yosys_techlibs_quicklogic)


add_share_file("share/quicklogic/common" "common/cells_sim.v")
add_share_file("share/quicklogic/pp3" "pp3/ffs_map.v")
add_share_file("share/quicklogic/pp3" "pp3/lut_map.v")
add_share_file("share/quicklogic/pp3" "pp3/latches_map.v")
add_share_file("share/quicklogic/pp3" "pp3/cells_map.v")
add_share_file("share/quicklogic/pp3" "pp3/cells_sim.v")
add_share_file("share/quicklogic/pp3" "pp3/abc9_model.v")
add_share_file("share/quicklogic/pp3" "pp3/abc9_map.v")
add_share_file("share/quicklogic/pp3" "pp3/abc9_unmap.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/arith_map.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/libmap_brams.txt")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/libmap_brams_map.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/brams_map.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/brams_sim.v")
#$(eval $(call add_gen_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/bram_types_sim.v))
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/cells_sim.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/ffs_map.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/dsp_sim.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/dsp_map.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/dsp_final_map.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/TDP18K_FIFO.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/ufifo_ctl.v")
add_share_file("share/quicklogic/qlf_k6n10f" "qlf_k6n10f/sram1024x18_mem.v")

