autoidx 1
twines
  leaf 1009 "everything.v"
  suffix 1010 1009 ":1.1-1.10"
  suffix 1011 1009 ":2.5-2.8"
  concat 1012 1010 1011
  leaf 1013 "tiny"
end
attribute \src "@1012"  # everything.v:1.1-1.10|everything.v:2.5-2.8
module $pub@1013  # \tiny
  attribute \src "@1010"  # everything.v:1.1-1.10
  wire input 1 \a
  attribute \src "@1011"  # everything.v:2.5-2.8
  wire output 2 \b
  connect \b \a
end
