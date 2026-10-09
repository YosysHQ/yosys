autoidx 1
twines
  leaf 1054 "everything"
  suffix 1055 1054 ".a"
  suffix 1056 1054 ".b"
  leaf 1057 "tiny"
end
module $pub@1057  # \tiny
  wire input 1 $pub@1055  # \everything.a
  wire output 2 $pub@1056  # \everything.b
  connect $pub@1056 $pub@1055  # \everything.b \everything.a
end
