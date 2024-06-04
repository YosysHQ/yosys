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
        yosys = pkgs.clangStdenv.mkDerivation {
          name = "yosys";
          src = ./. ;
          buildInputs = with pkgs; [ clang bison flex libffi tcl readline python3 llvmPackages.libcxxClang zlib git pkg-configUpstream ];
          checkInputs = with pkgs; [ gtest ];
          propagatedBuildInputs = [ abc-verifier ];
          preConfigure = "make config-clang";
          checkTarget = "test";
          installPhase = ''
            make install PREFIX=$out ABCEXTERNAL=yosys-abc
            ln -s ${abc-verifier}/bin/abc $out/bin/yosys-abc
          '';
					buildPhase = ''
            make -j$(nproc) ABCEXTERNAL=yosys-abc
          '';
          meta = with pkgs.lib; {
            description = "Yosys Open SYnthesis Suite";
            homepage = "https://yosyshq.net/yosys/";
            license = licenses.isc;
            maintainers = with maintainers; [ ];
          };
        };
        vcdiff = pkgs.stdenv.mkDerivation {
          pname = "vcdiff";
          version = "1.1";

          src = pkgs.fetchFromGitHub {
            owner = "orsonmmz";
            repo = "vcdiff";
            rev = "master";
            hash = "sha256-jTuok3TjuGW7+ATc11R9osKDPxbhRtuEbM8tRE4+AAI=";
          };

          buildInputs = [ pkgs.gcc ];

          installPhase = ''
          mkdir -p $out/bin
          cp vcdiff $out/bin/
        '';

          meta = with pkgs.lib; {
            description = "The ultimate VCD files comparator";
            license = licenses.gpl3;
            maintainers = with maintainers; [ orsonmmz ];
          };
        };
      in {
        packages.default = yosys;
        defaultPackage = yosys;
        packages.vcdiff = vcdiff;
        devShell = pkgs.mkShell {
          LOCALE_ARCHIVE_2_27 = "${pkgs.glibcLocales}/lib/locale/locale-archive";
          buildInputs = with pkgs; [ clang bison flex libffi tcl readline python3 llvmPackages.libcxxClang zlib git gtest abc-verifier gtkwave vcdiff lcov racket verilog z3 ];
        };
      }
    );
}
