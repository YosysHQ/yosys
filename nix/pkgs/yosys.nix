{
  bison,
  cmake,
  flex,
  gtest,
  lib,
  libffi,
  pkg-config,
  python3,
  readline,
  ninja,
  stdenv,
  tcl,
  zlib,
  src,
  rev,
  ...
}:

stdenv.mkDerivation {
  name = "yosys";
  inherit src;

  nativeBuildInputs = [
    bison
    cmake
    flex
    pkg-config
    python3
    ninja
  ];

  buildInputs = [
    gtest
    libffi
    readline
    tcl
    zlib
  ];

  cmakeFlags = [
    (lib.cmakeBool "YOSYS_SKIP_ABC_SUBMODULE_CHECK" true)
    (lib.cmakeFeature "YOSYS_CHECKOUT_INFO" rev)
  ];

  enableParallelBuilding = true;

  meta = with lib; {
    description = "Yosys Open SYnthesis Suite";
    homepage = "https://yosyshq.net/yosys/";
    license = licenses.isc;
  };
}
