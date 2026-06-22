{
  fetchurl,
  lib,
  pkgsBuildHost,
  stdenv,
}:

# Due to changes within the Tcl's TomMath vendored dependency, newer versions break building Yosys
# on Windows.
let
  version = "8.6.16";
  libver = lib.replaceString "." "" (lib.versions.majorMinor version);
in
stdenv.mkDerivation {
  pname = "tcl";
  inherit version;

  src = fetchurl {
    url = "mirror://sourceforge/tcl/tcl${version}-src.tar.gz";
    hash = "sha256-kcuPphdxxjwmLvtVMFm3x61nV6+lhXr2Jl5LC9wqFKU=";
  };

  preConfigure = ''
    cd win
  '';

  makeFlags = [
    "TCL_EXE=${lib.getExe' pkgsBuildHost.tcl "tclsh"}"
  ];

  # We only care for a subset of Tcl, this improves build times.
  buildFlags = [
    "binaries"
    "doc"
  ];

  installTargets = [
    "install-binaries"
    "install-libraries"
    "install-private-headers"
  ];

  enableParallelBuilding = true;

  postInstall = ''
    mkdir -p $out/lib/pkgconfig

    cat >$out/lib/pkgconfig/tcl.pc <<EOF
    # tcl pkg-config source file

    prefix=$out
    exec_prefix=$out
    libdir=$out/lib
    includedir=\''${prefix}/include
    libfile=libtcl${libver}.a

    Name: Tool Command Language
    Description: Tcl is a powerful, easy-to-learn dynamic programming language, suitable for a wide range of uses.
    URL: https://www.tcl-lang.org/
    Version: ${version}
    Libs: -L\''${libdir} -ltcl${libver} -ltclstub${libver}
    Libs.private: -luserenv -lws2_32 -lnetapi32
    Cflags: -I\''${includedir} -DUSE_TCL_STUBS
    EOF
  '';
}
