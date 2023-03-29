module top();
    // Examples from IEEE Std 1800-2017 21.2.1.3
    if ($sformatf(":%d:",  32'd10)   != ":        10:") $error;
    if ($sformatf(":%0d:", 32'd10)   != ":10:")         $error;
    if ($sformatf(":%h:",  32'd10)   != ":0000000a:")   $error;
    if ($sformatf(":%0h:", 32'd10)   != ":a:")          $error;
    if ($sformatf(":%3d:", 32'd5)    != ":  5:")        $error;
    if ($sformatf(":%3d:", 32'd100)  != ":100:")        $error;
    if ($sformatf(":%3d:", 32'd1234) != ":1234:")       $error;
    if ($sformatf(":%3h:", 32'h5)    != ":005:")        $error;
    if ($sformatf(":%3h:", 32'h100)  != ":100:")        $error;
    if ($sformatf(":%3h:", 32'h1234) != ":1234:")       $error;
    if ($sformatf(":%s:",  "abc")    != ":abc:")        $error;
    if ($sformatf(":%3s:", "a")      != ":  a:")        $error;
    if ($sformatf(":%3s:", "abc")    != ":abc:")        $error;
    if ($sformatf(":%3s:", "abcdef") != ":abcdef:")     $error;

    // Examples from IEEE Std 1800-2017 21.2.1.4
    if ($sformatf("%d",    1'bx)                               != "x")        $error;
    if ($sformatf("%h",    14'bx01010)                         != "XxXa")     $error;
    if ($sformatf("%h %o", 12'b001xxx101x01, 12'b001xxx101x01) != "XXX 1x5X") $error;

    // Octal format, testing unknown and high-impedance values.
    if ($sformatf(":%o:",  32'd10)                 != ":00000000012:") $error;
    if ($sformatf(":%0o:", 32'd10)                 != ":12:")          $error;
    if ($sformatf(":%o:",  21'bxxxzzz0x0zxz0z0)    != ":xxxzXXZ:")     $error;
    if ($sformatf(":%o:",  21'b101xxxzzz0x0zxz0z0) != ":05xzXXZ:")     $error;
    if ($sformatf(":%3o:", 21'b101xxxzzz0x0zxz0z0) != ":5xzXXZ:")      $error;  // Field expansion

    // Binary format
    if ($sformatf(":%b:",  8'b01xz) != ":000001xz:") $error;
    if ($sformatf(":%3b:", 8'b01xz) != ":1xz:")      $error;
endmodule
