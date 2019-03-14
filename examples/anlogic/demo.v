module demo (
    input wire CLK_IN,
    output wire R_LED
);
    parameter time1 = 30'd12_000_000;
    reg led_state;
    reg [29:0] count;

    always @(posedge CLK_IN)begin
        if(count == time1)begin
            count<= 30'd0;
            led_state <= ~led_state;
        end
        else
            count <= count + 1'b1;
    end
    assign R_LED = led_state;
endmodule
