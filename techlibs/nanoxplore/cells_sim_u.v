module NX_GCK_U(SI1, SI2, CMD, SO);
    input CMD;
    input SI1;
    input SI2;
    output SO;
    parameter inv_in = 1'b0;
    parameter inv_out = 1'b0;
    parameter std_mode = "BYPASS";

    wire SI1_int = inv_in ? ~SI1 : SI1;
    wire SI2_int = inv_in ? ~SI2 : SI2;

    wire SO_int;
    generate if (std_mode == "BYPASS") begin
        assign SO_int = SI1_int;
    end
    else if (std_mode == "MUX") begin
        assign SO_int = CMD ? SI1_int : SI2_int;
    end
    else if (std_mode == "CKS") begin
        assign SO_int = CMD ? SI1_int : 1'b0;
    end
    else if (std_mode == "CSC") begin
        assign SO_int = CMD;
    end
    else
    $error("Unrecognised std_mode");
    endgenerate
    assign SO = inv_out ? ~SO_int : SO_int;
endmodule
