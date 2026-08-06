autoidx 1
twines
  leaf 1054 "home"
  suffix 1055 1054 ".repo"
  suffix 1056 1055 ".chain"
  suffix 1057 1056 ".in"
  suffix 1058 1056 ".out"
end
module \chain
  wire input 1 $pub@1057  # \home.repo.chain.in
  wire output 2 $pub@1058  # \home.repo.chain.out
  connect $pub@1058 $pub@1057  # \home.repo.chain.out \home.repo.chain.in
end
