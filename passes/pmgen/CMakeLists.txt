add_library(yosys_passes_pmgen INTERFACE)

function(pmgen_command  _name _path)
    add_custom_command(
        OUTPUT ${CMAKE_BINARY_DIR}/${_path}/${_name}_pm.h
        COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/pmgen.py -o ${CMAKE_BINARY_DIR}/${_path}/${_name}_pm.h -p ${_name} ${CMAKE_SOURCE_DIR}/${_path}/${_name}.pmg
        DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/pmgen.py ${CMAKE_SOURCE_DIR}/${_path}/${_name}.pmg
        COMMENT "Generating ${_path}/${_name}_pm.h..."
    )
endfunction()

pmgen_command(test_pmgen passes/pmgen)
pmgen_command(ice40_dsp techlibs/ice40)
pmgen_command(ice40_wrapcarry techlibs/ice40)
pmgen_command(xilinx_dsp techlibs/xilinx)
pmgen_command(xilinx_dsp48a techlibs/xilinx)
pmgen_command(xilinx_dsp_CREG techlibs/xilinx)
pmgen_command(xilinx_dsp_cascade techlibs/xilinx)
pmgen_command(microchip_dsp techlibs/microchip)
pmgen_command(microchip_dsp_CREG techlibs/microchip)
pmgen_command(microchip_dsp_cascade techlibs/microchip)
pmgen_command(xilinx_srl techlibs/xilinx)

add_custom_command(
    OUTPUT ${CMAKE_BINARY_DIR}/passes/opt/peepopt_pm.h
    COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/pmgen.py -o ${CMAKE_BINARY_DIR}/passes/opt/peepopt_pm.h -p peepopt
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_shiftmul_right.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_shiftmul_left.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_shiftadd.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_muldiv.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_muldiv_c.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_formal_clockgateff.pmg
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/pmgen.py
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_shiftmul_right.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_shiftmul_left.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_shiftadd.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_muldiv.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_muldiv_c.pmg
        ${CMAKE_SOURCE_DIR}/passes/opt/peepopt_formal_clockgateff.pmg
    COMMENT "Generating passes/pmgen/peepopt_pm.h..."
)

target_sources(yosys_passes_pmgen INTERFACE
    test_pmgen.cc
    ${CMAKE_SOURCE_DIR}/techlibs/ice40/ice40_dsp.cc
    ${CMAKE_SOURCE_DIR}/techlibs/ice40/ice40_wrapcarry.cc
    ${CMAKE_SOURCE_DIR}/techlibs/xilinx/xilinx_dsp.cc
    ${CMAKE_SOURCE_DIR}/techlibs/microchip/microchip_dsp.cc
    ${CMAKE_SOURCE_DIR}/passes/opt/peepopt.cc
    ${CMAKE_SOURCE_DIR}/techlibs/xilinx/xilinx_srl.cc
)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/passes/pmgen/test_pmgen_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/ice40/ice40_dsp_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/ice40/ice40_wrapcarry_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/xilinx/xilinx_dsp_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/xilinx/xilinx_dsp48a_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/xilinx/xilinx_dsp_CREG_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/xilinx/xilinx_dsp_cascade_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/microchip/microchip_dsp_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/microchip/microchip_dsp_CREG_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/microchip/microchip_dsp_cascade_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/passes/opt/peepopt_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_BINARY_DIR}/techlibs/xilinx/xilinx_srl_pm.h)

target_link_libraries(yosys PRIVATE yosys_passes_pmgen)
