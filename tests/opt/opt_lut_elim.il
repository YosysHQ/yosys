module \test
  wire input 1 \i

  wire output 2 \o1
  cell $lut $1
    parameter \LUT 16'0110100110010110
    parameter \WIDTH 4
    connect \A { \i 3'000 }
    connect \Y \o1
  end

  wire output 2 \o2
  cell $lut $2
    parameter \LUT 16'0110100010010110
    parameter \WIDTH 4
    connect \A { \i 3'000 }
    connect \Y \o2
  end
end
