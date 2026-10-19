autoidx 1
twines
  leaf 1056 "everything"
  suffix 1057 1056 ".a"
  suffix 1058 1056 ".b"
  leaf 1059 "tiny"
end
module $pub@1059  # \tiny
  wire input 1 $pub@1057  # \everything.a
  wire output 2 $pub@1058  # \everything.b
  connect $pub@1058 $pub@1057  # \everything.b \everything.a
end
