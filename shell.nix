let
  lock = (builtins.fromJSON (builtins.readFile ./flake.lock)).nodes.nixpkgs.locked;
  nixpkgs = builtins.fetchTarball {
    url = "https://github.com/${lock.owner}/${lock.repo}/archive/${lock.rev}.tar.gz";
    sha256 = lock.narHash;
  };
  pkgs = import nixpkgs {
    config = { };
    overlays = [ ];
  };
  yosys = pkgs.callPackage ./nix/pkgs/yosys.nix {
    stdenv = pkgs.clangStdenv;
    src = null;
    rev = "unknown";
  };
in
import ./nix/shell.nix { inherit pkgs yosys; }
