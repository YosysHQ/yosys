This directory contains the runtime components of CXXRTL and should be placed on the include path
when building the simulation using the `-I${YOSYS}/backends/cxxrtl/runtime` option. These components
are not used in the Yosys binary; they are only built as a part of the simulation binary.

The interfaces declared in `cxxrtl_capi*.h` contain the stable C API. These interfaces will not be
changed in backward-incompatible ways unless no other option is available, and any breaking changes
will be made in a way that causes the downstream code to fail in a visible way. The ABI of these
interfaces is considered stable as well, and it will not use features complicating its use via
libraries such as libffi or ctypes.

The implementations in `cxxrtl_capi*.cc` are considered private; they are still placed in the include
path to enable build-system-less builds (where the CXXRTL runtime component is included in the C++
file of the simulation toplevel).

The interfaces declared in `cxxrtl*.h` (without `capi`) are unstable and may change without notice.

For clarity, all of the files in this directory and its subdirectories have unique names regardless
of the directory where they are placed.