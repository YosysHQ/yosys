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
