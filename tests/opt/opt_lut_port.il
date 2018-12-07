module $1
  wire width 4 input 2 \_0_
  wire output 4 \_1_
  wire input 3 \_2_
  wire output 1 \o
  cell $lut \_3_
    parameter \LUT 16'0011000000000011
    parameter \WIDTH 4
    connect \A { \_0_ [3] \o 2'00 }
    connect \Y \_1_
  end
  cell $lut \_4_
    parameter \LUT 4'0001
    parameter \WIDTH 4
    connect \A { 3'000 \_2_ }
    connect \Y \o
  end
end
