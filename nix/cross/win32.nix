{
  pkgs,
  overlays ? [ ],
}:

import pkgs.path {
  inherit (pkgs.stdenv.hostPlatform) system;
  crossSystem = pkgs.lib.systems.examples.mingw32 // {
    isStatic = true;
  };

  overlays = overlays ++ [
    (import ./win-overlay.nix)
  ];
}
