autoidx 1
metadata
  twines
    root 1055 "home"
    suffix 1056 1055 ".repo"
    suffix 1057 1056 ".chain"
    suffix 1058 1057 ".in"
    suffix 1059 1057 ".out"
  end
end
module \chain
  wire input 1 $pub@1058  # \home.repo.chain.in
  wire output 2 $pub@1059  # \home.repo.chain.out
  connect $pub@1059 $pub@1058  # \home.repo.chain.out \home.repo.chain.in
end
