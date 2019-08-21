module assert_dff(input clk, input test, input pat);
    always @(posedge clk)
    begin
        #1;
        if (test != pat)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time);
            $stop;
        end
    end
endmodule

module assert_tri(input en, input A, input B);
    always @(posedge en)
    begin
        #1;
        if (A !== B)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A," ",B);
            $stop;
        end
    end
endmodule

module assert_Z(input clk, input A);
    always @(posedge clk)
    begin
        #1;
        if (A === 1'bZ)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A);
            $stop;
        end
    end
endmodule

module assert_comb(input A, input B);
    always @(*)
    begin
        #1;
        if (A !== B)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A," ",B);
            $stop;
        end
    end
endmodule
