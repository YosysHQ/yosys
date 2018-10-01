#!/bin/bash

set -ex
vcxsrc="$1-$2"
yosysver="$2"
gitsha="$3"

rm -rf YosysVS-Tpl-v2.zip YosysVS
wget http://www.clifford.at/yosys/nogit/YosysVS-Tpl-v2.zip

unzip YosysVS-Tpl-v2.zip
rm -f YosysVS-Tpl-v2.zip
mv YosysVS "$vcxsrc"

{
	n=$(grep -B999 '<ItemGroup>' "$vcxsrc"/YosysVS/YosysVS.vcxproj | wc -l)
	head -n$n "$vcxsrc"/YosysVS/YosysVS.vcxproj
	egrep '\.(h|hh|hpp|inc)$' srcfiles.txt | sed 's,.*,<ClInclude Include="../yosys/&" />,'
	egrep -v '\.(h|hh|hpp|inc)$' srcfiles.txt | sed 's,.*,<ClCompile Include="../yosys/&" />,'
	echo '<ClCompile Include="../yosys/kernel/version.cc" />'
	tail -n +$((n+1)) "$vcxsrc"/YosysVS/YosysVS.vcxproj
} > "$vcxsrc"/YosysVS/YosysVS.vcxproj.new

mv "$vcxsrc"/YosysVS/YosysVS.vcxproj.new "$vcxsrc"/YosysVS/YosysVS.vcxproj

mkdir -p "$vcxsrc"/yosys
tar -cf - -T srcfiles.txt | tar -xf - -C "$vcxsrc"/yosys
cp -r share "$vcxsrc"/

echo "namespace Yosys { extern const char *yosys_version_str; const char *yosys_version_str=\"Yosys" \
		"$yosysver (git sha1 $gitsha, Visual Studio)\"; }" > "$vcxsrc"/yosys/kernel/version.cc

cat > "$vcxsrc"/readme-git.txt << EOT
Want to use a git working copy for the yosys source code?
Open "Git Bash" in this directory and run:

	mv yosys yosys.bak
	git clone https://github.com/cliffordwolf/yosys.git yosys
	cd yosys
	git checkout -B master $(git rev-parse HEAD | cut -c1-10)
	unzip ../genfiles.zip
EOT

cat > "$vcxsrc"/readme-abc.txt << EOT
Yosys is using "ABC" for gate-level optimizations and technology
mapping. Download yosys-win32-mxebin-$yosysver.zip and copy the
following files from it into this directory:

	pthreadVC2.dll
	yosys-abc.exe
EOT

sed -i 's/$/\r/; s/\r\r*/\r/g;' "$vcxsrc"/YosysVS/YosysVS.vcxproj "$vcxsrc"/readme-git.txt "$vcxsrc"/readme-abc.txt

