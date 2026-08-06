set -euo pipefail

mkdir -p temp

# If a different version of Yosys with different constids.inc wrote a file,
# the integers have to get remapped when read into this version
cat > temp/moved-static.il <<EOF
autoidx 1
twines
  leaf 42 "A"
  suffix 999999 42 ".sub"
end
module \$pub@999999
  wire input 1 \\a
end
EOF

${YOSYS} -p "read_rtlil temp/moved-static.il; write_rtlil temp/moved-static-out.il"
grep -q '# \\A.sub' temp/moved-static-out.il

cat > temp/stale-dynamic.il <<EOF
autoidx 1
twines
  leaf 3 "everything"
  suffix 4 3 ".sub"
  leaf 5 "tiny"
end
module \$pub@5
  wire input 1 \$pub@4
end
EOF

${YOSYS} -p "read_rtlil temp/stale-dynamic.il; write_rtlil temp/stale-dynamic-out.il"
grep -q '# \\tiny' temp/stale-dynamic-out.il
grep -q '# \\everything.sub' temp/stale-dynamic-out.il

${YOSYS} -p "read_rtlil temp/moved-static.il; write_rtlil temp/roundtrip.il"
grep -q 'leaf .* "A"' temp/roundtrip.il
