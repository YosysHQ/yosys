module task_global();

reg [7:0] temp_out;
reg [7:0] temp_in;

task convert;
begin
  temp_out = (9/5) *( temp_in + 32);
end
endtask

endmodule
