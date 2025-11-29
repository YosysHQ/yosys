package package_import_separate;

  localparam integer
    DATAWIDTH = 8,
    ADDRWIDTH = 4;

  localparam logic [2:0]
    IDLE  = 3'b000,
    START = 3'b001,
    DATA  = 3'b010,
    STOP  = 3'b100,
    DONE  = 3'b101;

endpackage
