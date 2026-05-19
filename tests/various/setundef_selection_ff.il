module \test
  wire input 1 \clk
  wire output 2 \a
  wire output 3 \b
  cell $dff \myff_a
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \a
    connect \Q \a
    connect \CLK \clk
  end
  cell $dff \myff_b
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D \b
    connect \Q \b
    connect \CLK \clk
  end
end
