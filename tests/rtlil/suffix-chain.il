autoidx 1
twines
  leaf 0 "/home/emil/repo/"
  suffix 1 0 "foo/"
  suffix 2 1 "bar.v"
  suffix 3 2 ":10.1-10.5"
  suffix 4 2 ":11.1-11.5"
end
module \chain
  attribute \src "@3"
  wire input 1 \a
  attribute \src "@4"
  wire output 2 \b
  connect \b \a
end
