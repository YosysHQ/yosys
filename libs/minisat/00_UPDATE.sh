#!/bin/bash

rm -f LICENSE *.cc *.h
git clone --depth 1 https://github.com/niklasso/minisat minisat_upstream
rm minisat_upstream/minisat/*/Main.cc
mv minisat_upstream/LICENSE minisat_upstream/minisat/*/*.{h,cc} .
rm -rf minisat_upstream

sed -i -e 's,^#include *"minisat/[^/]\+/\?,#include ",' *.cc *.h
sed -i -e 's/Minisat::memUsedPeak()/Minisat::memUsedPeak(bool)/' System.cc
sed -i -e 's/PRI[iu]64/ & /' Options.h Solver.cc
sed -i -e '1 i #ifndef __STDC_LIMIT_MACROS\n#define __STDC_LIMIT_MACROS\n#endif' *.cc
sed -i -e '1 i #ifndef __STDC_FORMAT_MACROS\n#define __STDC_FORMAT_MACROS\n#endif' *.cc

patch -p0 < 00_PATCH_mkLit_default_arg.patch
patch -p0 < 00_PATCH_remove_zlib.patch
patch -p0 < 00_PATCH_no_fpu_control.patch
patch -p0 < 00_PATCH_typofixes.patch

