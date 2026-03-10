module edges();
    (* anyseq *) reg [31:0] a, b, c;
    reg [31:0] o;
    reg NV, DZ, OF, UF, NX;
    symfpu mod (.*);

    wire [31:0] pos_max = 32'h7f7fffff;
    wire [31:0] pos_inf = 32'h7f800000;
    wire [31:0] neg_max = 32'hff7fffff;
    wire [31:0] neg_inf = 32'hff800000;

    wire a_sign = a[31];
    wire [30:0] a_unsigned = a[30:0];
    wire [7:0] a_exp = a[30:23];
    wire [22:0] a_sig = a[22:0];
    wire a_zero = a_unsigned == '0;
    wire a_special = a_exp == 8'hff;
    wire a_inf = a_special && a_sig == '0;
    wire a_nan = a_special && a_sig != '0;
    wire a_qnan = a_nan && a_sig[22] && a_sig[21:0] == '0;
    wire a_snan = a_nan && !a_sig[22];
    wire a_norm = a_exp > 8'h00 && !a_special;
    wire a_subnorm = a_exp == 8'h00 && a_sig != '0;
    wire a_finite = a_norm || a_subnorm;

    wire b_sign = b[31];
    wire [30:0] b_unsigned = b[30:0];
    wire [7:0] b_exp = b[30:23];
    wire [22:0] b_sig = b[22:0];
    wire b_zero = b_unsigned == '0;
    wire b_special = b_exp == 8'hff;
    wire b_inf = b_special && b_sig == '0;
    wire b_nan = b_special && b_sig != '0;
    wire b_qnan = b_nan && b_sig[22];
    wire b_snan = b_nan && !b_sig[22];
    wire b_norm = b_exp > 8'h00 && !b_special;
    wire b_subnorm = b_exp == 8'h00 && b_sig != '0;
    wire b_finite = b_norm || b_subnorm;

    wire c_sign = c[31];
    wire [30:0] c_unsigned = c[30:0];
    wire [7:0] c_exp = c[30:23];
    wire [22:0] c_sig = c[22:0];
    wire c_zero = c_unsigned == '0;
    wire c_special = c_exp == 8'hff;
    wire c_inf = c_special && c_sig == '0;
    wire c_nan = c_special && c_sig != '0;
    wire c_qnan = c_nan && c_sig[22];
    wire c_snan = c_nan && !c_sig[22];
    wire c_norm = c_exp > 8'h00 && !c_special;
    wire c_subnorm = c_exp == 8'h00 && c_sig != '0;
    wire c_finite = c_norm || c_subnorm;

    wire o_sign = o[31];
    wire [30:0] o_unsigned = o[30:0];
    wire [7:0] o_exp = o[30:23];
    wire [22:0] o_sig = o[22:0];
    wire o_zero = o_unsigned == '0;
    wire o_special = o_exp == 8'hff;
    wire o_inf = o_special && o_sig == '0;
    wire o_nan = o_special && o_sig != '0;
    wire o_qnan = o_nan && o_sig[22];
    wire o_snan = o_nan && !o_sig[22];
    wire o_norm = o_exp > 8'h00 && !o_special;
    wire o_subnorm = o_exp == 8'h00 && o_sig != '0;
    wire o_finite = o_norm || o_subnorm;
    wire o_unclamped = o_finite && o_unsigned != 31'h7f7fffff;

`ifdef MULADD
    wire muladd_zero = c_zero;
    wire a_is_1 = a == 32'h3f800000;
    wire b_is_1 = b == 32'h3f800000;
    wire use_lhs = a_is_1 || b_is_1;
    wire lhs_sign = b_is_1 ? a_sign : b_sign;
    wire [30:0] lhs_unsigned = b_is_1 ? a_unsigned : b_unsigned;
    wire [7:0] lhs_exp = b_is_1 ? a_exp : b_exp;
    wire [22:0] lhs_sig = b_is_1 ? a_sig : b_sig;
    wire lhs_zero = b_is_1 ? a_zero : b_zero;
    wire lhs_inf = b_is_1 ? a_inf : b_inf;
    wire lhs_nan = b_is_1 ? a_nan : b_nan;
    wire lhs_qnan = b_is_1 ? a_qnan : b_qnan;
    wire lhs_snan = b_is_1 ? a_snan : b_snan;
    wire lhs_norm = b_is_1 ? a_norm : b_norm;
    wire lhs_subnorm = b_is_1 ? a_subnorm : b_subnorm;
    wire lhs_finite = b_is_1 ? a_finite : b_finite;
    
    wire rhs_sign = c_sign;
    wire [30:0] rhs_unsigned = c_unsigned;
    wire [7:0] rhs_exp = c_exp;
    wire [22:0] rhs_sig = c_sig;
    wire rhs_zero = c_zero;
    wire rhs_inf = c_inf;
    wire rhs_nan = c_nan;
    wire rhs_qnan = c_qnan;
    wire rhs_snan = c_snan;
    wire rhs_norm = c_norm;
    wire rhs_subnorm = c_subnorm;
    wire rhs_finite = c_finite;
`else
    wire muladd_zero = 1;
    wire use_lhs = 1;
    wire lhs_sign = a_sign;
    wire [30:0] lhs_unsigned = a_unsigned;
    wire [7:0] lhs_exp = a_exp;
    wire [22:0] lhs_sig = a_sig;
    wire lhs_zero = a_zero;
    wire lhs_inf = a_inf;
    wire lhs_nan = a_nan;
    wire lhs_qnan = a_qnan;
    wire lhs_snan = a_snan;
    wire lhs_norm = a_norm;
    wire lhs_subnorm = a_subnorm;
    wire lhs_finite = a_finite;
    
    wire rhs_sign = b_sign;
    wire [30:0] rhs_unsigned = b_unsigned;
    wire [7:0] rhs_exp = b_exp;
    wire [22:0] rhs_sig = b_sig;
    wire rhs_zero = b_zero;
    wire rhs_inf = b_inf;
    wire rhs_nan = b_nan;
    wire rhs_qnan = b_qnan;
    wire rhs_snan = b_snan;
    wire rhs_norm = b_norm;
    wire rhs_subnorm = b_subnorm;
    wire rhs_finite = b_finite;
`endif

`ifdef SUB
    wire is_sub = lhs_sign == rhs_sign;
`else
    wire is_sub = lhs_sign != rhs_sign;
`endif
    wire lhs_dominates = lhs_exp > rhs_exp;
    wire [7:0] exp_diff = lhs_dominates ? lhs_exp - rhs_exp : rhs_exp - lhs_exp;

    wire round_p_001, round_p_011, round_n_001, round_n_011;
    wire [30:0] rounded_100, rounded_010, rounded_000;

`ifdef MUL
    assign round_p_001 = 0;
    assign round_p_011 = a == 32'h40400000 && b == 32'h40000001;
    assign round_n_001 = 0;
    assign round_n_011 = a == 32'hc0400000 && b == 32'h40000001;

    assign rounded_100 = 31'h40C00002;
    assign rounded_010 = 31'h40C00001;
    assign rounded_000 = 31'h40C00000;
`elsif ADD
    assign round_p_001 = a == 32'h4c000000 && b == 32'h40000000;
    assign round_p_011 = a == 32'h4c000001 && b == 32'h40000000;
    assign round_n_001 = a == 32'hcc000000 && b == 32'hc0000000;
    assign round_n_011 = a == 32'hcc000001 && b == 32'hc0000000;

    assign rounded_100 = 31'h4C000002;
    assign rounded_010 = 31'h4C000001;
    assign rounded_000 = 31'h4C000000;
`else
    assign round_p_001 = 0;
    assign round_p_011 = 0;
    assign round_n_001 = 0;
    assign round_n_011 = 0;

    assign rounded_100 = '0;
    assign rounded_010 = '0;
    assign rounded_000 = '0;
`endif

    always @* begin
        if (a_nan || b_nan || c_nan) begin
            // input NaN = output NaN
            assert (o_nan);

		    // NaN inputs give NaN outputs, do not raise exceptions (unless signaling NV)
            // assert (!DZ);
            // assert (!OF);
            // assert (!UF);
            // assert (!NX);
        end

        if (a_snan)
            // signalling NaN raises invalid exception
            assert (NV);

        if (a_qnan && b_qnan && c_qnan)
            // quiet NaN inputs do not raise invalid exception
            assert (!NV);

        if (DZ)
            // output = +-inf
            assert (o_inf);

        if (NV)
            // output = qNaN
            assert (o_qnan);

        if (OF)
            // overflow is always inexact
            assert (NX);

        if (UF)
            // underflow is always inexact
            assert (NX);

`ifdef RNE
        if (OF) // output = +-inf
            assert (o_inf);
`elsif RNA
        if (OF) // output = +-inf
            assert (o_inf);
`elsif RTP
        if (OF) // output = +inf or -max
            assert (o == pos_inf || o == neg_max);
        if (o == neg_inf)
            assert (!OF);
`elsif RTN
        if (OF) // output = +max or -inf
            assert (o == pos_max || o == neg_inf);
        if (o == pos_inf)
            assert (!OF);
`elsif RTZ
        if (OF) // output = +-max
            assert (o == pos_max || o == neg_max);
        if (o_inf) // cannot overflow to infinity 
            assert (!OF);
`endif

        if (UF)
            // output = subnormal
            assert (o_subnorm);

        if (o_inf && !OF)
            // a non-overflowing infinity is exact
            assert (!NX);

        if (o_subnorm && !UF)
            // a non-underflowing subnormal is exact
            assert (!NX);

`ifdef DIV
        assume (c_zero);
        // a = finite, b = 0
        if ((a_norm || a_subnorm) && b_unsigned == '0)
            assert (DZ);
        // 0/0 or inf/inf
        if ((a_zero && b_zero) || (a_inf && b_inf))
            assert (NV);
        // dividing by a very small number will overflow
        if (a_norm && a_exp > 8'h80 && b == 32'h00000001)
            assert (OF);
        // dividing by a much smaller number will overflow
        if (a_norm && b_finite && lhs_dominates && exp_diff > 8'h80)
            assert (OF);
        // dividing by a much larger number will hit 0 bias
        if (a_finite && b_norm && !lhs_dominates && exp_diff > 8'h7f) begin
            assert (o_exp == '0);
            // if the divisor is large enough, underflow (or zero) is guaranteed
            if (exp_diff > 8'h95) begin
                assert (NX);
                assert (UF || o_zero);
            end
        end
`endif

`ifdef MUL
        assume (c_zero);
`endif

`ifdef MULS
        // 0/inf or inf/0
        if ((a_inf && b_zero) || (a_zero && b_inf))
            assert (NV);
        // very large multiplications overflow
        if (a_unsigned == 31'h7f400000 && b_unsigned == a_unsigned && !c_special)
            assert (OF);
        // multiplying a small number by an even smaller number will underflow
        if (a_norm && a_exp < 8'h60 && b_subnorm && !c_special) begin
            assert (NX);
    `ifdef MULADD
            // within rounding
            assert (UF || (c_zero ? o_zero : (o == c || o == c+1 || o == c-1)));
    `else
            assert (UF || o_zero);
            if (o_zero)
                assert (o_sign == a_sign ^ b_sign);
    `endif
        end
`endif

`ifdef ADDSUB
        assume (c_zero);
        // adder can't underflow, subnormals are always exact
        assert (!UF);
`endif

`ifdef RNE
        if (round_p_001) assert (o_unsigned == rounded_000);
        if (round_p_011) assert (o_unsigned == rounded_100);
        if (round_n_001) assert (o_unsigned == rounded_000);
        if (round_n_011) assert (o_unsigned == rounded_100);
`elsif RNA
        if (round_p_001) assert (o_unsigned == rounded_010);
        if (round_p_011) assert (o_unsigned == rounded_100);
        if (round_n_001) assert (o_unsigned == rounded_010);
        if (round_n_011) assert (o_unsigned == rounded_100);
`elsif RTP
        if (round_p_001) assert (o_unsigned == rounded_010);
        if (round_p_011) assert (o_unsigned == rounded_100);
        if (round_n_001) assert (o_unsigned == rounded_000);
        if (round_n_011) assert (o_unsigned == rounded_010);
`elsif RTN
        if (round_p_001) assert (o_unsigned == rounded_000);
        if (round_p_011) assert (o_unsigned == rounded_010);
        if (round_n_001) assert (o_unsigned == rounded_010);
        if (round_n_011) assert (o_unsigned == rounded_100);
`elsif RTZ
        if (round_p_001) assert (o_unsigned == rounded_000);
        if (round_p_011) assert (o_unsigned == rounded_010);
        if (round_n_001) assert (o_unsigned == rounded_000);
        if (round_n_011) assert (o_unsigned == rounded_010);
`endif

`ifdef ADDS
        if (use_lhs) begin
            // inf - inf
            if (lhs_inf && rhs_inf && is_sub)
                assert (NV);
            // very large additions overflow
            if (lhs_unsigned == 31'h7f400000 && rhs_unsigned == lhs_unsigned && !is_sub)
                assert (OF);
            // if the difference in exponent is more than the width of the mantissa,
            // the result cannot be exact
            if (lhs_finite && rhs_finite && exp_diff > 8'd24)
                assert (NX || OF);
            if (!UF) begin
                // for a small difference in exponent with zero LSB, the result must be
                // exact
                if (o_unclamped && lhs_dominates && exp_diff < 8'd08 && rhs_sig[7:0] == 0 && lhs_sig[7:0] == 0)
                    assert (!NX);
                if (exp_diff == 0 && !OF && lhs_sig[7:0] == 0 && rhs_sig[7:0] == 0)
                    assert (!NX);
            end
            // there's probably a better general case for this, but a moderate
            // difference in exponent with non zero LSB must be inexact
            if (o_finite && lhs_dominates && exp_diff > 8'd09 && rhs_sig[7:0] != 0 && lhs_sig[7:0] == 0)
                assert (NX);
        end
`endif

`ifdef MULADD
        // not sure how to check this in the generic case since we don't have the partial mul
        if ((a_inf || b_inf) && !(a_nan || b_nan) && c_inf && (a_sign ^ b_sign ^ c_sign))
            assert (NV);
        // normal multiplication, overflow addition
        if (a == 31'h5f400000 && b == a && c == 32'h7f400000) begin
            assert (OF);
            assert (o_inf); // assuming RNE
        end
        // if multiplication overflows, addition can bring it back in range
        if (a == 32'hc3800001 && b == 32'h7b800000 && !c_special) begin
            if (c_sign)
                // result is negative, so a negative addend can't
                assert (OF);
            else if (c_exp <= 8'he7)
                // addend can't be too small
                assert (OF);
            else if (c_exp == 8'he8 && c_sig <= 22'h200000)
                // this is just the turning point for this particular value
                assert (OF);
            else
                // a large enough positive addend will never overflow (but is
                // still likely to be inexact)
                assert (!OF);
        end
`endif

`ifdef SQRT
        assume (b_zero);
        assume (c_zero);
        // complex roots are invalid
        if (a_sign && (a_norm || a_subnorm))
            assert (NV);
`endif

    end
endmodule