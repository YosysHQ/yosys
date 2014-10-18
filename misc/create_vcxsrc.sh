#!/bin/bash

set -ex
vcxsrc="$1"

rm -rf YosysVS-Tpl-v1.zip YosysVS
wget http://www.clifford.at/yosys/nogit/YosysVS-Tpl-v1.zip

unzip YosysVS-Tpl-v1.zip
rm -f YosysVS-Tpl-v1.zip
mv YosysVS "$vcxsrc"

{
	n=$(grep -B999 '<ItemGroup>' "$vcxsrc"/YosysVS/YosysVS.vcxproj | wc -l)
	head -n$n "$vcxsrc"/YosysVS/YosysVS.vcxproj
	egrep '\.(h|hh|hpp|inc)$' srcfiles.txt | sed 's,.*,<ClInclude Include="../yosys/&" />,'
	egrep -v '\.(h|hh|hpp|inc)$' srcfiles.txt | sed 's,.*,<ClCompile Include="../yosys/&" />,'
	tail -n +$((n+1)) "$vcxsrc"/YosysVS/YosysVS.vcxproj
} > "$vcxsrc"/YosysVS/YosysVS.vcxproj.new

mv "$vcxsrc"/YosysVS/YosysVS.vcxproj.new "$vcxsrc"/YosysVS/YosysVS.vcxproj

mkdir -p "$vcxsrc"/yosys
tar -cf - -T srcfiles.txt | tar -xf - -C "$vcxsrc"/yosys

cat > "$vcxsrc"/readme-git.txt << EOT
Using a git working copy for the yosys source code:

Open "Git Bash" in this directory and run:

	mv yosys yosys.bak
	git clone https://github.com/cliffordwolf/yosys.git yosys
	cd yosys
	git checkout -B master $(git rev-parse HEAD | cut -c1-10)
	unzip ../genfiles.zip
EOT

sed -i 's/$/\r/; s/\r\r*/\r/g;' "$vcxsrc"/YosysVS/YosysVS.vcxproj "$vcxsrc"/readme-git.txt

