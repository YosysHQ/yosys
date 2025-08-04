package config_pkg;
  localparam integer
    DATA_WIDTH = 8,
    ADDR_WIDTH = 4;
    
  localparam logic [2:0]
    IDLE = 3'b000,
    START = 3'b001,
    DATA = 3'b010,
    ODD_PARITY = 3'b011,
    STOP = 3'b100,
    DONE = 3'b101;
endpackage 