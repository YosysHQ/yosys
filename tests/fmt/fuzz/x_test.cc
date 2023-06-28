#include "fuzztest/fuzztest.h"
#include "gtest/gtest.h"

#include <sstream>
#include "backends/cxxrtl/cxxrtl.h"
#include "libs/bigint/BigUnsigned.hh"

using namespace cxxrtl_yosys;

void Formats128BitUnsignedIntegers(uint64_t x, uint64_t y) {
  // Compare output to actual BigUnsigned.
  value<64> vs;
  value<128> v;
  vs.set(x);
  v = v.blit<127, 64>(vs);
  vs.set(y);
  v = v.blit<63, 0>(vs);

  std::ostringstream oss;
  oss << value_formatted<128>(v, false, false, ' ', 0, 10, false, false, false);
  auto actual = oss.str();

  BigUnsigned b(x);
  b.bitShiftLeft(b, 64);
  b.bitOr(b, y);

  std::string expected;

  if (b.isZero()) {
    expected = "0";
  } else {
    while (!b.isZero()) {
      expected += '0' + (b % 10).toInt();
      b /= 10;
    }
    std::reverse(expected.begin(), expected.end());
  }

  EXPECT_EQ(actual, expected);
}
FUZZ_TEST(CxxrtlDivisionFuzz, Formats128BitUnsignedIntegers);

