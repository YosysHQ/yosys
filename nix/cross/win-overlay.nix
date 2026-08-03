(final: prev: {
  # Fix for static linking.
  readline = prev.readline.overrideAttrs (
    oldAttrs:
    prev.lib.attrsets.optionalAttrs prev.stdenv.hostPlatform.isMinGW {
      NIX_CFLAGS_COMPILE = "-DNEED_EXTERN_PC=1";
    }
  );

  tcl = if final.stdenv.hostPlatform.isMinGW then final.callPackage ./tcl.nix { } else prev.tcl;

  # Create a pc file for termcap, since readline expects it.
  termcap = prev.termcap.overrideAttrs (
    oldAttrs:
    prev.lib.attrsets.optionalAttrs prev.stdenv.hostPlatform.isMinGW {
      postInstall = oldAttrs.postInstall + ''
        mkdir -p $dev/lib/pkgconfig/

        cat >$dev/lib/pkgconfig/termcap.pc <<EOF
        prefix=$out
        libdir=\''${prefix}/lib
        includedir=$dev/include

        Name: Termcap
        Description: GNU Termcap library and data base that enables programs to use display terminals in a terminal-independent manner
        URL: https://www.gnu.org/software/termutils/
        Version: ${oldAttrs.version}
        Libs: -L\''${libdir} -ltermcap
        Cflags -I\''${includedir}
        EOF
      '';
    }
  );

  # Use pthreads on Windows.
  threads = final.lib.optionalAttrs final.stdenv.targetPlatform.isMinGW {
    model = "posix";
    package = null;
  };

  windows = prev.windows.overrideScope (
    finalScope: prevScope: {
      # Make sure we actually have pthreads available.
      mingw_w64 = prevScope.mingw_w64.overrideAttrs (oldAttrs: {
        configureFlags = oldAttrs.configureFlags ++ [
          "--with-libraries=winpthreads"
        ];
      });
    }
  );
})
