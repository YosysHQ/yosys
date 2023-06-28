cmake_minimum_required(VERSION 3.14)
project(cxxrtl_division_fuzz)

set(CMAKE_CXX_STANDARD 17)

add_subdirectory(fuzztest)

enable_testing()

include(GoogleTest)

fuzztest_setup_fuzzing_flags()

include_directories(../../..)

add_executable(
    x_test
    x_test.cc
    ../../../libs/bigint/BigUnsigned.cc
)

link_fuzztest(x_test)
gtest_discover_tests(x_test)
