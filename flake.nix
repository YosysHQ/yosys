{
  description = "A nix flake for the Yosys synthesis suite";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        # TODO: don't override src when ./abc is empty
        # which happens when the command used is `nix build` and not `nix build ?submodules=1`
        abc-verifier = pkgs.abc-verifier.overrideAttrs(x: y: {src = ./abc;});
        yosys = pkgs.llvmPackages.libcxxStdenv.mkDerivation {
          name = "yosys";
          src = ./. ;
          buildInputs = with pkgs; [ bison flex libffi tcl readline python3 zlib git pkg-configUpstream tracy ];
          checkInputs = with pkgs; [ gtest ];
          propagatedBuildInputs = [ abc-verifier ];
          preConfigure = "make config-clang";
          checkTarget = "test";
          installPhase = ''
            make install PREFIX=$out ABCEXTERNAL=yosys-abc STRIP=\#
            ln -s ${abc-verifier}/bin/abc $out/bin/yosys-abc
          '';
					buildPhase = ''
            make -j$(nproc) ABCEXTERNAL=yosys-abc PROFILER=tracy
          '';
          dontStrip = true;
          meta = with pkgs.lib; {
            description = "Yosys Open SYnthesis Suite";
            homepage = "https://yosyshq.net/yosys/";
            license = licenses.isc;
            maintainers = with maintainers; [ ];
          };
        };
      in {
        packages.default = yosys;
        defaultPackage = yosys;
        devShell = pkgs.mkShell.override {stdenv = pkgs.llvmPackages.libcxxStdenv; } {
          buildInputs = with pkgs; [ bison flex libffi tcl readline python3 zlib git pkg-configUpstream tracy ];
          propagatedBuildInputs = [ abc-verifier ];
        };
      }
    );
}
