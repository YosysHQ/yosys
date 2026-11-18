{ pkgs, yosys }:

pkgs.mkShell.override { stdenv = yosys.stdenv; } {
  inputsFrom = [
    yosys
  ];

  packages = with pkgs; [
    llvmPackages.clang-tools
    llvmPackages.bintools
    iverilog
    gtkwave
    (python3.withPackages (ps: [
      ps.pybind11
      ps.cxxheaderparser
      ps.click
    ]))
  ];

  shellHook = ''
    DRIVER_ROOT="${yosys.stdenv.cc}/bin"
    export CLANGD_FLAGS="--query-driver $DRIVER_ROOT/$CC,$DRIVER_ROOT/$CXX"
  '';
}
