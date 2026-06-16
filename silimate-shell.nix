{ pkgs ? import <nixpkgs> {} }:
	let libs = pkgs.libs;
	binutils = pkgs.binutils;
	gnu-ar = pkgs.stdenvNoCC.mkDerivation {
		# match homebrew name
		pname = "gnu-ar";
		inherit (binutils) version;

		buildInputs = [ binutils ];

		phases = ["installPhase"];

		installPhase = ''
			mkdir -p $out/bin
			ln -s ${binutils}/bin/ar $out/bin/gar
		'';
	};
in
pkgs.mkShell {
	buildInputs = with pkgs; [
		bison
		flex
		cmake
		eigen
		swig
		boost
		libedit
		pkg-config
		m4
		cmake
		ninja
		tcl
		libffi
		nodejs
		gawk
		gperf
		autoconf
		libdwarf # provides libdwarf.so
		libelf # provides libelf.a
		doxygen
		cudd
		zlib
		clang
		iverilog # tests
		gtkwave # vcd2fst
		(python3.withPackages(ps: with ps; [pybind11 cxxheaderparser]))
		gnu-ar
		gtest
	] ++ lib.optionals stdenv.isLinux [
		elfutils # provides libdw.so (not to be confused with libdwarf.so)
	];

	cmakeFlags = [ "-DCMAKE_C_COMPILER=clang" "-DCMAKE_CXX_COMPILER=clang++" "-DCMAKE_BUILD_TYPE=Debug" "-DCMAKE_CXX_FLAGS=-O0" "-DYOSYS_WITH_PYTHON:BOOL=ON" ];
}
