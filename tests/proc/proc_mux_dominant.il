module \nonexhaustive
  wire width 2 input 1 \s
  wire width 3 input 2 \a
  wire width 3 output 3 \y
  wire width 3 $0\y
  process $proc
    assign $0\y \y
    attribute \full_case 1
    switch \s
      case 2'00
        assign $0\y 3'110
      case 2'01
        assign $0\y \a
      case 2'10
        assign $0\y \a
    end
    sync always
      update \y $0\y
  end
end

module \exhaustive
  wire width 2 input 1 \s
  wire width 3 input 2 \a
  wire width 3 output 3 \y
  wire width 3 $0\y
  process $proc
    assign $0\y \y
    attribute \full_case 1
    switch \s
      case 2'00
        assign $0\y 3'110
      case 2'01
        assign $0\y \a
      case 2'10
        assign $0\y \a
      case 2'11
        assign $0\y \a
    end
    sync always
      update \y $0\y
  end
end
