autoidx 1
twines
  leaf 1053 "home"
  suffix 1054 1053 ".repo"
  suffix 1055 1054 ".chain"
  suffix 1056 1055 ".in"
  suffix 1057 1055 ".out"
end
module \chain
  wire input 1 $pub@1056  # \home.repo.chain.in
  wire output 2 $pub@1057  # \home.repo.chain.out
  connect $pub@1057 $pub@1056  # \home.repo.chain.out \home.repo.chain.in
end
