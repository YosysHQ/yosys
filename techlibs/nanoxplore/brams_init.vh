function [409600-1:0] bram_init_to_string;
    input [49152-1:0] array;
    input integer blocks;
    input integer width;
    reg [409600-1:0] temp; // (49152+2048)*8 48K bit data + 2k commas
    reg [24-1:0] temp2; 
    integer i;
    integer j;
begin
    temp = "";
    for (i = 0; i < 2048; i = i + 1) begin
        if (i != 0) begin
            temp = {temp, ","};
        end
        temp2 = 24'b0;
        for (j = 0; j < blocks; j = j + 1) begin
            temp2[j*width +: width] = array[{j, i[10:0]}*width +: width];
        end
        temp = {temp, $sformatf("%b",temp2[23:0])};
    end
    bram_init_to_string = temp;
end
endfunction
