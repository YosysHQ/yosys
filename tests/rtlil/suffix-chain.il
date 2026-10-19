autoidx 1
twines
  leaf 1056 "home"
  suffix 1057 1056 ".repo"
  suffix 1058 1057 ".chain"
  suffix 1059 1058 ".in"
  suffix 1060 1058 ".out"
end
module \chain
  wire input 1 $pub@1059  # \home.repo.chain.in
  wire output 2 $pub@1060  # \home.repo.chain.out
  connect $pub@1060 $pub@1059  # \home.repo.chain.out \home.repo.chain.in
end
