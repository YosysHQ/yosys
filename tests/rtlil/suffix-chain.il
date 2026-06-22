autoidx 1
twines
  leaf 1009 "/home/emil/repo/"
  suffix 1010 1009 "foo/"
  suffix 1011 1010 "bar.v"
  suffix 1012 1011 ":10.1-10.5"
  suffix 1013 1011 ":11.1-11.5"
end
module \chain
  attribute \src "@1012"  # /home/emil/repo/foo/bar.v:10.1-10.5
  wire input 1 \a
  attribute \src "@1013"  # /home/emil/repo/foo/bar.v:11.1-11.5
  wire output 2 \b
  connect \b \a
end
