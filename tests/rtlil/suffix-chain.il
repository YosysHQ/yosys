autoidx 1
twines
  leaf 1014 "/home/emil/repo/"
  suffix 1015 1014 "foo/"
  suffix 1016 1015 "bar.v"
  suffix 1017 1016 ":10.1-10.5"
  suffix 1018 1016 ":11.1-11.5"
end
module \chain
  attribute \src "@1017"  # /home/emil/repo/foo/bar.v:10.1-10.5
  wire input 1 \a
  attribute \src "@1018"  # /home/emil/repo/foo/bar.v:11.1-11.5
  wire output 2 \b
  connect \b \a
end
