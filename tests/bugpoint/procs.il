module \ff_with_en_and_sync_reset
  wire $0\q[1:1]
  wire $0\q[0:0]
  attribute \raise_error 4
  wire width 2 output 5 \q
  wire width 2 input 4 \d
  wire input 3 \enable
  wire input 2 \reset
  wire input 1 \clock

  process \proc_a
    assign $0\q[0:0] \q [0]
    switch \reset
      case 1'1
        assign $0\q[0:0] 1'0
      case 
        switch \enable
          case 1'1
            assign $0\q[0:0] \d [0]
          case 
        end
    end
    sync posedge \clock
      update \q [0] $0\q[0:0]
  end

  process \proc_b
    assign $0\q[1:1] \q [1]
    switch \reset
      case 1'1
        assign $0\q[1:1] 1'0
      case 
        switch \enable
          case 1'1
            assign $0\q[1:1] \d [1]
          case 
        end
    end
    sync posedge \clock
      update \q [1] $0\q[1:1]
  end
end
