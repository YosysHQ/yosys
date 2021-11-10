module top;
    wire logic wire_logic_0; assign wire_logic_0 = 0;
    wire logic wire_logic_1; assign wire_logic_1 = 1;
    wand logic wand_logic_0; assign wand_logic_0 = 0; assign wand_logic_0 = 1;
    wand logic wand_logic_1; assign wand_logic_1 = 1; assign wand_logic_1 = 1;
    wor logic wor_logic_0; assign wor_logic_0 = 0; assign wor_logic_0 = 0;
    wor logic wor_logic_1; assign wor_logic_1 = 1; assign wor_logic_1 = 0;

    wire integer wire_integer; assign wire_integer = 4'b1001;
    wand integer wand_integer; assign wand_integer = 4'b1001; assign wand_integer = 4'b1010;
    wor integer wor_integer; assign wor_integer = 4'b1001; assign wor_integer = 4'b1010;

    typedef logic [3:0] typename;
    wire typename wire_typename; assign wire_typename = 4'b1001;
    wand typename wand_typename; assign wand_typename = 4'b1001; assign wand_typename = 4'b1010;
    wor typename wor_typename; assign wor_typename = 4'b1001; assign wor_typename = 4'b1010;

    always @* begin
        assert (wire_logic_0 == 0);
        assert (wire_logic_1 == 1);
        assert (wand_logic_0 == 0);
        assert (wand_logic_1 == 1);
        assert (wor_logic_0 == 0);
        assert (wor_logic_1 == 1);

        assert (wire_integer == 4'b1001);
        assert (wand_integer == 4'b1000);
        assert (wor_integer == 4'b1011);

        assert (wire_typename == 4'b1001);
        assert (wand_typename == 4'b1000);
        assert (wor_typename == 4'b1011);
    end
endmodule
