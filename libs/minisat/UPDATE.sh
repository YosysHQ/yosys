#!/bin/bash

rm -f LICENSE *.cc *.h
git clone --depth 1 https://github.com/niklasso/minisat minisat_upstream
rm minisat_upstream/minisat/*/Main.cc
mv minisat_upstream/LICENSE minisat_upstream/minisat/*/*.{h,cc} .
rm -rf minisat_upstream

sed -i -e 's,^#include *"minisat/[^/]\+,#include "libs/minisat,' *.cc *.h
sed -i -e 's/Minisat::memUsedPeak()/Minisat::memUsedPeak(bool)/' System.cc
sed -i -e 's/PRI[iu]64/ & /' Options.h Solver.cc
sed -i -e '1 i #define __STDC_LIMIT_MACROS' *.cc
sed -i -e '1 i #define __STDC_FORMAT_MACROS' *.cc

patch -p0 < PATCH_mkLit_default_arg.patch

