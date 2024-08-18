{
  description = "A nix flake for the Yosys synthesis suite with cross-compilation support";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachSystem [
      flake-utils.lib.system.x86_64-linux
      flake-utils.lib.system.aarch64-linux
      flake-utils.lib.system.x86_64-darwin
      flake-utils.lib.system.aarch64-darwin
    ] (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        
        build-yosys = (pkgs: rec {
          abc-verifier = pkgs.abc-verifier.overrideAttrs(x: y: {src = ./abc;});
          yosys = pkgs.clangStdenv.mkDerivation {
            pname = "yosys";
            version = "0.23";
            src = ./.;
            buildInputs = with pkgs; [ clang bison flex libffi tcl readline python3 llvmPackages.libcxxClang zlib git pkg-config llvmPackages.bintools ];
            checkInputs = with pkgs; [ gtest ];
            propagatedBuildInputs = [ abc-verifier ];
            preConfigure = "make config-clang";
            checkTarget = "test";
            installPhase = ''
              make install PREFIX=$out ABCEXTERNAL=yosys-abc
              ln -s ${abc-verifier}/bin/abc $out/bin/yosys-abc
            '';
            buildPhase = ''
              make -j$NIX_BUILD_CORES ABCEXTERNAL=yosys-abc
            '';
            meta = with pkgs.lib; {
              description = "Yosys Open SYnthesis Suite";
              homepage = "https://yosyshq.net/yosys/";
              license = licenses.isc;
              maintainers = with maintainers; [ ];
              platforms = platforms.unix;
            };
          };
        });

        # Function to build for a specific system
        buildForSystem = targetSystem: 
          let
            crossPkgs = import nixpkgs {
              inherit system;
              crossSystem = nixpkgs.lib.systems.examples.${targetSystem};
            };
          in
          (build-yosys crossPkgs).yosys;

      in
      {
        packages = {
          default = (build-yosys pkgs).yosys;
          yosys = (build-yosys pkgs).yosys;
          yosys-aarch64-linux = buildForSystem "aarch64-multiplatform";
          yosys-aarch64-darwin = buildForSystem "aarch64-darwin";
        };
      }
    );
}