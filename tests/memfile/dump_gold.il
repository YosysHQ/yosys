module \gold
  wire input 1 \clk
  wire input 1 \wen
  wire input 3 \addr
  wire input 4 \wdata
  wire input 4 \rdata
  cell $__MEMORY \m
    parameter \WIDTH 4
    parameter \ABITS 3
    parameter \INIT 32'11011110101011011011111011101111
    connect \PORT_A_CLK \clk
    connect \PORT_A_ADDR \addr
    connect \PORT_A_WR_DATA \wdata
    connect \PORT_A_WR_EN \wen
    connect \PORT_A_RD_DATA \rdata
  end
end
