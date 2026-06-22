autoidx 1
twines
  leaf 1014 "everything.v"
  suffix 1015 1014 ":1.1-1.10"
  suffix 1016 1014 ":2.5-2.8"
  concat 1017 1015 1016
  leaf 1018 "tiny"
end
attribute \src "@1017"  # everything.v:1.1-1.10|everything.v:2.5-2.8
module $pub@1018  # \tiny
  attribute \src "@1015"  # everything.v:1.1-1.10
  wire input 1 \a
  attribute \src "@1016"  # everything.v:2.5-2.8
  wire output 2 \b
  connect \b \a
end
