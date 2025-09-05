autoidx 15
attribute \src "everything.v:1.1-32.10"
attribute \cells_not_processed 1
module \alu
  attribute \src "everything.v:2.8-2.11"
  wire input 1 \clk
  attribute \src "everything.v:3.14-3.15"
  wire width 8 input 2 \A
  attribute \src "everything.v:4.14-4.15"
  wire width 8 input 3 \B
  attribute \src "everything.v:5.14-5.23"
  wire width 4 input 4 \operation
  attribute \src "everything.v:6.19-6.25"
  wire width 8 output 5 \result
  attribute \src "everything.v:7.13-7.15"
  wire output 6 \CF
  attribute \src "everything.v:8.13-8.15"
  wire output 7 \ZF
  attribute \src "everything.v:9.13-9.15"
  wire output 8 \SF
  attribute \src "everything.v:15.12-15.15"
  wire width 9 \tmp
  attribute \src "everything.v:17.2-31.5"
  wire width 8 $0\result[7:0]
  attribute \src "everything.v:17.2-31.5"
  wire $0\CF[0:0]
  attribute \src "everything.v:17.2-31.5"
  wire $0\ZF[0:0]
  attribute \src "everything.v:17.2-31.5"
  wire $0\SF[0:0]
  attribute \src "everything.v:17.2-31.5"
  wire width 9 $0\tmp[8:0]
  attribute \src "everything.v:17.2-31.5"
  wire width 9 $1\tmp[8:0]
  attribute \src "everything.v:21.11-21.16"
  wire width 9 $add$everything.v:21$2_Y
  attribute \src "everything.v:23.11-23.16"
  wire width 9 $sub$everything.v:23$3_Y
  attribute \src "everything.v:27.9-27.22"
  wire $eq$everything.v:27$4_Y
  attribute \src "everything.v:21.11-21.16"
  cell $add $add$everything.v:21$2
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 9
    connect \A \A
    connect \B \B
    connect \Y $add$everything.v:21$2_Y
  end
  attribute \src "everything.v:23.11-23.16"
  cell $sub $sub$everything.v:23$3
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 9
    connect \A \A
    connect \B \B
    connect \Y $sub$everything.v:23$3_Y
  end
  attribute \src "everything.v:27.9-27.22"
  cell $eq $eq$everything.v:27$4
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_WIDTH 32
    parameter \Y_WIDTH 1
    connect \A $1\tmp[8:0] [7:0]
    connect \B 0
    connect \Y $eq$everything.v:27$4_Y
  end
  attribute \src "everything.v:17.2-31.5"
  process $proc$everything.v:17$1
    assign { } { }
    assign { } { }
    assign { } { }
    assign { } { }
    assign { } { }
    assign $0\tmp[8:0] $1\tmp[8:0]
    assign $0\CF[0:0] $1\tmp[8:0] [8]
    assign $0\ZF[0:0] $eq$everything.v:27$4_Y
    assign $0\SF[0:0] $1\tmp[8:0] [7]
    assign $0\result[7:0] $1\tmp[8:0] [7:0]
    attribute \src "everything.v:19.3-24.10"
    switch \operation
    attribute \src "everything.v:19.19-19.19"
      case 4'0000
        assign { } { }
        assign $1\tmp[8:0] $add$everything.v:21$2_Y
    attribute \src "everything.v:21.17-21.17"
      case 4'0001
        assign { } { }
        assign $1\tmp[8:0] $sub$everything.v:23$3_Y
      case 
        assign $1\tmp[8:0] \tmp
    end
    sync posedge \clk
      update \result $0\result[7:0]
      update \CF $0\CF[0:0]
      update \ZF $0\ZF[0:0]
      update \SF $0\SF[0:0]
      update \tmp $0\tmp[8:0]
  end
end
attribute \src "everything.v:34.1-40.10"
attribute \cells_not_processed 1
module \foo
  attribute \src "everything.v:35.17-35.18"
  wire width 8 input 1 \a
  attribute \src "everything.v:35.32-35.33"
  wire width 8 input 2 \b
  attribute \src "everything.v:35.48-35.49"
  wire width 8 output 3 \y
  attribute \src "everything.v:37.16-37.18"
  wire width 8 \bb
  attribute \src "everything.v:39.16-39.22"
  wire width 8 $add$everything.v:39$5_Y
  attribute \src "everything.v:39.16-39.22"
  cell $add $add$everything.v:39$5
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 8
    connect \A \a
    connect \B \bb
    connect \Y $add$everything.v:39$5_Y
  end
  connect \b \bb
  connect \y $add$everything.v:39$5_Y
end
attribute \cells_not_processed 1
attribute \src "everything.v:1.1-32.10"
module \zzz
  attribute \src "everything.v:27.9-27.22"
  wire $eq$everything.v:27$4_Y
  attribute \src "everything.v:23.11-23.16"
  wire width 9 $sub$everything.v:23$3_Y
  attribute \src "everything.v:21.11-21.16"
  wire width 9 $add$everything.v:21$2_Y
  attribute \src "everything.v:17.2-31.5"
  wire width 9 $1\tmp[8:0]
  attribute \src "everything.v:17.2-31.5"
  wire width 9 $0\tmp[8:0]
  attribute \src "everything.v:17.2-31.5"
  wire $0\SF[0:0]
  attribute \src "everything.v:17.2-31.5"
  wire $0\ZF[0:0]
  attribute \src "everything.v:17.2-31.5"
  wire $0\CF[0:0]
  attribute \src "everything.v:17.2-31.5"
  wire width 8 $0\result[7:0]
  attribute \src "everything.v:15.12-15.15"
  wire width 9 \tmp
  attribute \src "everything.v:9.13-9.15"
  wire output 8 \SF
  attribute \src "everything.v:8.13-8.15"
  wire output 7 \ZF
  attribute \src "everything.v:7.13-7.15"
  wire output 6 \CF
  attribute \src "everything.v:6.19-6.25"
  wire width 8 output 5 \result
  attribute \src "everything.v:5.14-5.23"
  wire width 4 input 4 \operation
  attribute \src "everything.v:4.14-4.15"
  wire width 8 input 3 \B
  attribute \src "everything.v:3.14-3.15"
  wire width 8 input 2 \A
  attribute \src "everything.v:2.8-2.11"
  wire input 1 \clk
  wire $procmux$8_CMP
  wire width 9 $procmux$7_Y
  wire $procmux$9_CMP
  attribute \src "everything.v:27.9-27.22"
  cell $logic_not $eq$everything.v:27$4
    parameter \A_SIGNED 0
    parameter \Y_WIDTH 1
    parameter \A_WIDTH 8
    connect \A $1\tmp[8:0] [7:0]
    connect \Y $eq$everything.v:27$4_Y
  end
  attribute \src "everything.v:23.11-23.16"
  cell $sub $sub$everything.v:23$3
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 9
    connect \A \A
    connect \B \B
    connect \Y $sub$everything.v:23$3_Y
  end
  attribute \src "everything.v:21.11-21.16"
  cell $add $add$everything.v:21$2
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 9
    connect \A \A
    connect \B \B
    connect \Y $add$everything.v:21$2_Y
  end
  attribute \src "everything.v:21.17-21.17|everything.v:19.3-24.10"
  attribute \full_case 1
  cell $eq $procmux$8_CMP0
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 4
    parameter \B_WIDTH 4
    parameter \Y_WIDTH 1
    connect \A \operation
    connect \B 4'0001
    connect \Y $procmux$8_CMP
  end
  attribute \src "everything.v:21.17-21.17|everything.v:19.3-24.10"
  attribute \full_case 1
  cell $pmux $procmux$7
    parameter \WIDTH 9
    parameter \S_WIDTH 2
    connect \A \tmp
    connect \B { $add$everything.v:21$2_Y $sub$everything.v:23$3_Y }
    connect \S { $procmux$9_CMP $procmux$8_CMP }
    connect \Y $procmux$7_Y
  end
  attribute \src "everything.v:19.19-19.19|everything.v:19.3-24.10"
  attribute \full_case 1
  cell $logic_not $procmux$9_CMP0
    parameter \A_SIGNED 0
    parameter \Y_WIDTH 1
    parameter \A_WIDTH 4
    connect \A \operation
    connect \Y $procmux$9_CMP
  end
  attribute \src "everything.v:17.2-31.5"
  cell $dff $procdff$10
    parameter \WIDTH 8
    parameter \CLK_POLARITY 1'1
    connect \D $procmux$7_Y [7:0]
    connect \Q \result
    connect \CLK \clk
  end
  attribute \src "everything.v:17.2-31.5"
  cell $dff $procdff$11
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D $procmux$7_Y [8]
    connect \Q \CF
    connect \CLK \clk
  end
  attribute \src "everything.v:17.2-31.5"
  cell $dff $procdff$12
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D $eq$everything.v:27$4_Y
    connect \Q \ZF
    connect \CLK \clk
  end
  attribute \src "everything.v:17.2-31.5"
  cell $dff $procdff$13
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1'1
    connect \D $procmux$7_Y [7]
    connect \Q \SF
    connect \CLK \clk
  end
  attribute \src "everything.v:17.2-31.5"
  cell $dff $procdff$14
    parameter \WIDTH 9
    parameter \CLK_POLARITY 1'1
    connect \D $procmux$7_Y
    connect \Q \tmp
    connect \CLK \clk
  end
  connect $0\result[7:0] $1\tmp[8:0] [7:0]
  connect $0\SF[0:0] $1\tmp[8:0] [7]
  connect $0\ZF[0:0] $eq$everything.v:27$4_Y
  connect $0\CF[0:0] $1\tmp[8:0] [8]
  connect $0\tmp[8:0] $1\tmp[8:0]
  connect $1\tmp[8:0] $procmux$7_Y
end
