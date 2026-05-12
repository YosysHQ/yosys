{
  pkgs,
  overlays ? [ ],
}:

import pkgs.path {
  inherit (pkgs.stdenv.hostPlatform) system;
  crossSystem = pkgs.lib.systems.examples.mingwW64 // {
    isStatic = true;
  };

  overlays = overlays ++ [
    (import ./win-overlay.nix)
  ];
}
