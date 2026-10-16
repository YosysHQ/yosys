autoidx 1
twines
  leaf 1054 "everything.v"
  suffix 1055 1054 ":1.1-1.10"
  suffix 1056 1054 ":2.5-2.8"
  leaf 1057 "tiny"
end
srcs
  set 0 1055
  set 1 1056
  set 2 1055 1056
end
attribute \src "@2"  # everything.v:1.1-1.10|everything.v:2.5-2.8
module $pub@1057  # \tiny
  attribute \src "@0"  # everything.v:1.1-1.10
  wire input 1 \a
  attribute \src "@1"  # everything.v:2.5-2.8
  wire output 2 \b
  connect \b \a
end
