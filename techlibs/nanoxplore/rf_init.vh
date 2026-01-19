function [9728-1:0] rf_init_to_string;
    input [1152-1:0] array;
    input integer blocks;
    input integer width;
    reg [9728-1:0] temp; // (1152+1152/18)*8
    integer i;
begin
    temp = "";
    for (i = 0; i < blocks; i = i + 1) begin
    if (i != 0) begin
        temp = {temp, ","};
    end
    temp = {temp, $sformatf("%b",array[(i+1)*width-1: i*width])};
    end
    rf_init_to_string = temp;
end
endfunction
