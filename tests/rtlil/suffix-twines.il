autoidx 1
twines
  leaf 1053 "everything"
  suffix 1054 1053 ".a"
  suffix 1055 1053 ".b"
  leaf 1056 "tiny"
end
module $pub@1056  # \tiny
  wire input 1 $pub@1054  # \everything.a
  wire output 2 $pub@1055  # \everything.b
  connect $pub@1055 $pub@1054  # \everything.b \everything.a
end
