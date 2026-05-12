{
  description = "A Nix flake for the Yosys synthesis suite.";

  inputs = {
    # This requires Nix >= 2.27.0.
    self.submodules = true;

    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;

          overlays = [
            (final: prev: {
              yosys = final.callPackage ./nix/pkgs/yosys.nix {
                src = self;
                rev = (self.shortRev or self.dirtyShortRev or "unknown");
              };
            })
          ];
        };

        yosys-clang = pkgs.yosys.override { stdenv = pkgs.clangStdenv; };

        win32Pkgs = pkgs.callPackage ./nix/cross/win32.nix { };
        win64Pkgs = pkgs.callPackage ./nix/cross/win64.nix { };

        mkShell =
          t:
          pkgs.mkShell.override { stdenv = t.stdenv; } {
            inputsFrom = [
              t
            ];

            packages = with pkgs; [
              llvmPackages.clang-tools
            ];

            shellHook = ''
              DRIVER_ROOT="${t.stdenv.cc}/bin"
              export CLANGD_FLAGS="--query-driver $DRIVER_ROOT/$CC,$DRIVER_ROOT/$CXX"
            '';
          };
      in
      {
        formatter = pkgs.nixfmt-tree;

        devShells = rec {
          shell = mkShell yosys-clang;
          shell-gcc = mkShell pkgs.yosys;
          shell-win32 = mkShell win32Pkgs.yosys;
          shell-win64 = mkShell win64Pkgs.yosys;

          default = shell;
        };

        packages = rec {
          yosys = yosys-clang;
          yosys-gcc = pkgs.yosys;
          yosys-win32 = win32Pkgs.yosys;
          yosys-win64 = win64Pkgs.yosys;

          default = yosys;
        };
      }
    );
}
