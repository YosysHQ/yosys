module v2k_reg();

// v2k allows to init variables
reg a = 0;
// Here only last variable is set to 0, i.e d = 0
// Rest b, c are set to x
reg b, c, d = 0;
// reg data type can be signed in v2k
// We can assign with signed constants
reg signed [7:0] data = 8'shF0;

// Function can return signed values
// Its ports can contain signed ports
function signed [7:0] adder;
  input a_in;
  input b_in;
  input c_in;
  input signed [7:0] data_in;
  begin
    adder = a_in + b_in + c_in + data_in;
  end
endfunction

endmodule
