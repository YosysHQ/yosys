add_library(yosys_passes_pmgen INTERFACE)

function(pmgen_command  _name)
    add_custom_command(
        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${_name}_pm.h
        COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/pmgen.py -o ${CMAKE_CURRENT_BINARY_DIR}/${_name}_pm.h -p ${_name} ${CMAKE_CURRENT_SOURCE_DIR}/${_name}.pmg
        DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/pmgen.py ${CMAKE_CURRENT_SOURCE_DIR}/${_name}.pmg
        COMMENT "Generating passes/pmgen/${_name}_pm.h..."
    )
endfunction()

pmgen_command(test_pmgen)
pmgen_command(ice40_dsp)
pmgen_command(ice40_wrapcarry)
pmgen_command(xilinx_dsp)
pmgen_command(xilinx_dsp48a)
pmgen_command(xilinx_dsp_CREG)
pmgen_command(xilinx_dsp_cascade)
pmgen_command(microchip_dsp)
pmgen_command(microchip_dsp_CREG)
pmgen_command(microchip_dsp_cascade)
pmgen_command(xilinx_srl)

add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/peepopt_pm.h
    COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/pmgen.py -o ${CMAKE_CURRENT_BINARY_DIR}/peepopt_pm.h -p peepopt
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_shiftmul_right.pmg
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_shiftmul_left.pmg
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_shiftadd.pmg
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_muldiv.pmg
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_formal_clockgateff.pmg
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/pmgen.py
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_shiftmul_right.pmg
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_shiftmul_left.pmg
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_shiftadd.pmg
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_muldiv.pmg
        ${CMAKE_CURRENT_SOURCE_DIR}/peepopt_formal_clockgateff.pmg
    COMMENT "Generating passes/pmgen/peepopt_pm.h..."
)

target_sources(yosys_passes_pmgen INTERFACE
    test_pmgen.cc
    ice40_dsp.cc
    ice40_wrapcarry.cc
    xilinx_dsp.cc
    microchip_dsp.cc
    peepopt.cc
    xilinx_srl.cc
)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/test_pmgen_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/ice40_dsp_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/ice40_wrapcarry_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/xilinx_dsp_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/xilinx_dsp48a_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/xilinx_dsp_CREG_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/xilinx_dsp_cascade_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/microchip_dsp_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/microchip_dsp_CREG_pm.h)
target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/microchip_dsp_cascade_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/peepopt_pm.h)

target_sources(yosys_passes_pmgen PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/xilinx_srl_pm.h)

target_link_libraries(yosys PRIVATE yosys_passes_pmgen)
