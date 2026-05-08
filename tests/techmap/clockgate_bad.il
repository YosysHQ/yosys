module \bad1
  wire input 1 \clk
  wire input 3 \d1
  wire input 2 \en
  wire output 4 \q1
  cell $dffe $auto$ff.cc:266:slice$27
    parameter \CLK_POLARITY 1
    parameter \EN_POLARITY 1
    parameter \WIDTH 1
    connect \CLK \clk
    connect \D \d1
    connect \EN 1'1
    connect \Q \q1
  end
end

module \bad2
  wire input 1 \clk
  wire input 3 \d1
  wire input 2 \en
  wire output 4 \q1
  cell $dffe $auto$ff.cc:266:slice$27
    parameter \CLK_POLARITY 1
    parameter \EN_POLARITY 1
    parameter \WIDTH 1
    connect \CLK 1'1
    connect \D \d1
    connect \EN \en
    connect \Q \q1
  end
end