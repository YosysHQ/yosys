autoidx 1
metadata
  twines
    root 1055 "everything"
    suffix 1056 1055 ".a"
    suffix 1057 1055 ".b"
    root 1058 "tiny"
  end
end
module $pub@1058  # \tiny
  wire input 1 $pub@1056  # \everything.a
  wire output 2 $pub@1057  # \everything.b
  connect $pub@1057 $pub@1056  # \everything.b \everything.a
end
