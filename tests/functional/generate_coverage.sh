#!/bin/bash

# Ensure you have compiled with coverage flags
# g++ -o vcd_harness -fprofile-arcs -ftest-coverage vcd_harness.cpp

# Define the directory two levels below the current directory
coverage_dir="../../"

# Create directory for coverage report
mkdir -p coverage_report

# Capture coverage data from the specified directory, excluding external libraries
lcov --capture --directory "$coverage_dir" --output-file coverage_report/vcd_harness.info --no-external

# Generate HTML report
genhtml coverage_report/vcd_harness.info --output-directory coverage_report

# Open the HTML report in the default web browser
xdg-open coverage_report/index.html
