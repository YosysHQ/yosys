autoidx 1
metadata
  twines
    root 1053 "everything.v"
    suffix 1054 1053 ":1.1-1.10"
    suffix 1055 1053 ":2.5-2.8"
    root 1056 "tiny"
  end
  srcs
    set 0 1054
    set 1 1055
    set 2 1054 1055
  end
end
attribute \src "@2"  # everything.v:1.1-1.10|everything.v:2.5-2.8
module $pub@1056  # \tiny
  attribute \src "@0"  # everything.v:1.1-1.10
  wire input 1 \a
  attribute \src "@1"  # everything.v:2.5-2.8
  wire output 2 \b
  connect \b \a
end
