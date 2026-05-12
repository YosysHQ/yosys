include(CTest)
include(GoogleTest)

function(yosys_gtest arg_TARGET)
	cmake_parse_arguments(PARSE_ARGV 1 arg "" "" "COMPONENTS")
	set(arg_SOURCES ${arg_UNPARSED_ARGUMENTS})

	set(target "gtest-${arg_TARGET}")
	add_executable(${target} ${arg_SOURCES})
	target_link_libraries(${target} PRIVATE GTest::gmock_main yosys_common)
	yosys_expand_components(test_components essentials ${arg_COMPONENTS})
	yosys_link_components(${target} PRIVATE ${test_components})
	gtest_discover_tests(${target})
endfunction()

if (GTest_FOUND)
	add_subdirectory(kernel)
	add_subdirectory(opt)
	add_subdirectory(techmap)

	enable_testing()
endif()
