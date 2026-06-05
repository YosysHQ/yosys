autoidx 1
twines
  leaf 0 "everything.v"
  suffix 1 0 ":1.1-1.10"
  suffix 2 0 ":2.5-2.8"
  concat 3 1 2
end
attribute \src "@3"
module \tiny
  attribute \src "@1"
  wire input 1 \a
  attribute \src "@2"
  wire output 2 \b
  connect \b \a
end
