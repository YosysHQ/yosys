`default_nettype none
module testcase (input wire clk, input wire [3:0] dataWriteCmd_payload_mask, input wire _zz_1_,
	         input wire [9:0] dataWriteCmd_payload_address,
	         input wire [31:0] dataWriteCmd_payload_data,
		 input wire _zz_5_, io_cpu_writeBack_isStuck,
		 output reg [31:0] io_cpu_writeBack_data,
		 input wire  [9:0] dataReadCmd_payload);


  (* ram_style = "block" *) reg [7:0] ways_0_data_symbol0 [0:1023];
  (* ram_style = "block" *) reg [7:0] ways_0_data_symbol1 [0:1023];
  (* ram_style = "block" *) reg [7:0] ways_0_data_symbol2 [0:1023];
  (* ram_style = "block" *) reg [7:0] ways_0_data_symbol3 [0:1023];

  reg [7:0] _zz_24_;
  reg [7:0] _zz_25_;
  reg [7:0] _zz_26_;
  reg [7:0] _zz_27_;
  reg [31:0] _zz_11_;
  wire [31:0] stageB_dataMux;
  reg [31:0] stageB_dataReadRsp_0;
  wire [31:0] ways_0_dataReadRsp;

  always @ (*) begin
    _zz_11_ = {_zz_27_, _zz_26_, _zz_25_, _zz_24_};
  end

  always @ (posedge clk) begin
    if(dataWriteCmd_payload_mask[0] && _zz_1_) begin
      ways_0_data_symbol0[dataWriteCmd_payload_address] <= dataWriteCmd_payload_data[7 : 0];
    end
    if(dataWriteCmd_payload_mask[1] && _zz_1_) begin
      ways_0_data_symbol1[dataWriteCmd_payload_address] <= dataWriteCmd_payload_data[15 : 8];
    end
    if(dataWriteCmd_payload_mask[2] && _zz_1_) begin
      ways_0_data_symbol2[dataWriteCmd_payload_address] <= dataWriteCmd_payload_data[23 : 16];
    end
    if(dataWriteCmd_payload_mask[3] && _zz_1_) begin
      ways_0_data_symbol3[dataWriteCmd_payload_address] <= dataWriteCmd_payload_data[31 : 24];
    end
  end

  always @ (posedge clk) begin
    if(_zz_5_) begin
      _zz_24_ <= ways_0_data_symbol0[dataReadCmd_payload];
      _zz_25_ <= ways_0_data_symbol1[dataReadCmd_payload];
      _zz_26_ <= ways_0_data_symbol2[dataReadCmd_payload];
      _zz_27_ <= ways_0_data_symbol3[dataReadCmd_payload];
    end
  end

assign stageB_dataMux = stageB_dataReadRsp_0;
assign ways_0_dataReadRsp = _zz_11_;

always @(posedge clk) begin
if((! io_cpu_writeBack_isStuck))begin
      stageB_dataReadRsp_0 <= ways_0_dataReadRsp;
    end
end

always @(*)
  io_cpu_writeBack_data = stageB_dataMux;

endmodule

