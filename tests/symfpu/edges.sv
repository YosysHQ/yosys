module edges(input clk);

`ifdef MASK
    (* anyseq *) reg [31:0] a_in, b_in, c_in;
    wire [31:0] a, b, c;
    assign a = a_in & 32'hffc42108;
    assign b = b_in & 32'hfff80001;
    assign c = c_in & 32'hfff80001;
`elsif MAP
    (* anyseq *) reg [31:0] a_pre, b_pre, c_pre;
    wire [31:0] a_in, b_in, c_in;
    // assuming 8/24
    assign a_in[31:22] = a_pre[31:22];
    assign b_in[31:22] = b_pre[31:22];
	assign a_in[21:0] = (a_pre[21:0] & 22'h042100) | (|(a_pre[21:0] & ~22'h042100) << 3);
	assign b_in[21:0] = (b_pre[21:0] & 22'h380000) | (|(b_pre[21:0] & ~22'h380000) << 0);
    assign c_in = c_pre;

    wire [31:0] a, b, c;
    assign a = a_in & 32'hffc42108;
    assign b = b_in & 32'hfff80001;
    assign c = c_in & 32'hfff80001;
`else
    (* anyseq *) reg [31:0] a, b, c;
`endif

    (* anyseq *) reg [4:0] rm;
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

    wire signed [8:0] a_sexp = $signed({1'b0, a_exp}) - 8'h7f;
    wire signed [8:0] half_a_sexp = a_sexp >>> 1;

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
    wire o_clamped = o_unsigned == 31'h7f7fffff;
    wire o_unclamped = o_finite && !o_clamped;
    wire o_ebmin = o_exp == 8'h01 && o_sig == '0;

    wire signed [8:0] o_sexp = $signed({1'b0, o_exp}) - 8'h7f;

    (* keep *) wire [25:0] a_faux = {2'b10, !a_subnorm, a_sig};
    (* keep *) wire [25:0] b_faux = {2'b00, !b_subnorm, b_sig};
    (* keep *) wire [25:0] o_faux = (a_faux - b_faux);

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

`ifdef MAX
    wire choose_max = 1;
`else
    wire choose_max = 0;
`endif

    wire rm_RNE = rm[0] == 1'b1;
    wire rm_RNA = rm[1:0] == 2'b10;
    wire rm_RTP = rm[2:0] == 3'b100;
    wire rm_RTN = rm[3:0] == 4'b1000;
    wire rm_RTZ = rm[4:0] == 5'b10000;

    wire c_muladd_turning = rm_RNE || rm_RNA ? c_sig <= 23'h200000 :
        rm_RTP ? c_sig == '0 :
        rm_RTN ? c_sig < 23'h400000 :
        c_sig == '0;

    always @* begin
        // all classes of input are possible (for all inputs)
        cover (a_sign);
        cover (!a_sign);
        cover (a_zero);
        cover (a_norm);
        cover (a_subnorm);
        cover (a_inf);
        cover (a_qnan);
        cover (a_snan);

`ifndef SQRTS
// sqrt has no b input
        cover (b_sign);
        cover (!b_sign);
        cover (b_zero);
        cover (b_norm);
        cover (b_subnorm);
        cover (b_inf);
        cover (b_qnan);
        cover (b_snan);
`endif

`ifdef MULADD
// only muladd has c input
        cover (c_sign);
        cover (!c_sign);
        cover (c_zero);
        cover (c_norm);
        cover (c_subnorm);
        cover (c_inf);
        cover (c_qnan);
        cover (c_snan);
`endif

        // all flags are possible
        cover (NV);
`ifndef COMPARES
    `ifdef DIVS
    // only div can div/zero
        cover (DZ);
    `endif
    `ifndef SQRTS
    // sqrt can't overflow or underflow
        cover (OF);
        `ifndef ADDSUB
        // add/sub can't underflow
        cover (UF);
        `endif
    `endif
        cover (NX);
`endif
        cover (!NV);
        cover (!DZ);
        cover (!OF);
        cover (!UF);
        cover (!NX);

        // all classes of output are possible
        cover (o_sign);
        cover (!o_sign);
        cover (o_zero);
        cover (o_norm);
        cover (o_inf);
        cover (o_nan);
`ifndef SQRTS
// subnormal outputs not possible for 8/24 sqrt
        cover (o_subnorm);
        cover (o_ebmin);
`endif

`ifndef COMPARES
`ifndef SQRTS
        if (OF) begin
            cover (o_inf);
            cover (o_clamped);
        end else begin
            cover (o_inf);
            cover (o_clamped);
        end

        if (UF) begin
    `ifndef ADDSUB
            cover (o_zero);
            cover (o_ebmin);
            cover (o_subnorm);
    `endif
        end else begin
            cover (o_zero);
            cover (o_ebmin);
            cover (o_subnorm);
        end

        if (NX) begin
            cover (o_norm);
            cover (o_inf);
    `ifndef ADDSUB
            cover (o_subnorm);
            cover (o_zero);
    `endif
        end
`endif

        if (a_nan || b_nan || c_nan) begin
            // input NaN = output NaN
            assert (o_nan);

		    // NaN inputs give NaN outputs, do not raise exceptions (unless signaling NV)
            assert (!DZ);
            assert (!OF);
            assert (!UF);
            assert (!NX);
        end

        if (NV)
            // output = qNaN
            assert (o_qnan);
`endif // !COMPARES

        if (a_snan || b_snan)
            // signalling NaN raises invalid exception
            assert (NV);

        if (a_qnan && b_qnan && c_qnan)
            // quiet NaN inputs do not raise invalid exception
            assert (!NV);

        if (DZ)
            // output = +-inf
            assert (o_inf);

        if (OF)
            // overflow is always inexact
            assert (NX);

        if (UF)
            // underflow is always inexact
            assert (NX);

        if (UF)
            // output = subnormal or zero or +-e^bmin
            assert (o_subnorm || o_zero || o_ebmin);

        if (o_inf && !OF)
            // a non-overflowing infinity is exact
            assert (!NX);

        if (o_subnorm && !UF)
            // a non-underflowing subnormal is exact
            assert (!NX);

`ifdef COMPARES
        assume (c_zero);
        assert (!OF);
        assert (!UF);
        assert (!NX);
        assert (!DZ);

        if (!a_nan && b_nan)
            assert (o == a);
        else if (a_nan && !b_nan)
            assert (o == b);
        else if (a_nan && b_nan)
            assert (o_nan);
        else begin
            assert (o == a || o == b);

            if (a_inf) begin
                if (a_sign == choose_max)
                    assert (o == b);
                else
                    assert (o == a);
            end

            if (b_inf) begin
                if (b_sign == choose_max)
                    assert (o == a);
                else
                    assert (o == b);
            end
        end

        if (!a_special && !b_special) begin
            if (a_sign != b_sign)
                if (a_sign == choose_max)
                    assert (o == b);
                else
                    assert (o == a);
            // a_sign == b_sign
            else if (a_exp != b_exp)
                if ((a_exp > b_exp) ^ a_sign ^ choose_max)
                    assert (o == b);
                else
                    assert (o == a);
            // a_exp == b_exp
            else if ((a_sig > b_sig) ^ a_sign ^ choose_max)
                assert (o == b);
            else
                assert (o == a);
        end
`endif

`ifdef DIVS
        assume (c_zero);
        // div/zero only when a is finite
        assert (DZ ^~ (a_finite && b_zero));
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
        // an unrounded result between +-e^bmin is still an underflow when rounded to ebmin
        if (a_unsigned == 31'h0031b7be && b_unsigned == 31'h3ec6def9)
            assert (UF);
    `ifdef ALTDIV
        if (!NV && !NX && !a_special && b_finite && o_norm)
            // if o is subnorm then it can be shifted arbitrarily depending on exponent difference
            assert (o_sig == (o_faux[25] ? o_faux[24:2] : o_faux[23:1]));
    `endif
`endif

`ifdef MUL
        assume (c_zero);
        // an unrounded result between +-e^bmin is still an underflow when rounded to ebmin
        if (a_unsigned == 31'h0ffffffd && b_unsigned == 31'h30000001) begin
            assert (UF);
            // but it's only ebmin when rounded towards the nearest infinity
            assert (o_ebmin ^~ (o_sign ? rm_RTN : rm_RTP));
        end
`endif

`ifdef MULS
        if (a_unsigned == 31'h0ffffffd && b_unsigned == 31'h30000001 && c_subnorm)
            if (!c_sign ^ b_sign ^ a_sign)
                assert (!UF);
            else
                assert (UF);
        // 0/inf or inf/0
        if ((a_inf && b_zero) || (a_zero && b_inf))
            assert (NV);
        // very large multiplications overflow
        if (a_unsigned == 31'h7f400000 && b_unsigned == a_unsigned && !c_special)
            assert (OF);
        // multiplying a small number by an even smaller number will underflow
        if (a_norm && a_exp < 8'h68 && b_subnorm && !c_special) begin
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
        assume (rm_RNE);
`elsif RNA
        assume (rm_RNA);
`elsif RTP
        assume (rm_RTP);
`elsif RTN
        assume (rm_RTN);
`elsif RTZ
        assume (rm_RTZ);
`else
        assume ($onehot(rm));
`endif

        if (OF)
            // rounding mode determines if overflow value is inf or max
            casez (rm)
                5'bzzzz1 /* RNE */: assert (o_inf);
                5'bzzz10 /* RNA */: assert (o_inf);
                5'bzz100 /* RTP */: assert (o == pos_inf || o == neg_max);
                5'bz1000 /* RTN */: assert (o == pos_max || o == neg_inf);
                5'b10000 /* RTZ */: assert (o == pos_max || o == neg_max);
            endcase

        // RTx modes cannot underflow to the opposite ebmin (or either for RTZ)
        if (UF && o_ebmin)
            if (o_sign)
                assert (rm_RNE || rm_RNA || rm_RTN);
            else
                assert (rm_RNE || rm_RNA || rm_RTP);

        // and the same for overflowing to infinities
        if (OF && o_inf)
            if (o_sign)
                assert (rm_RNE || rm_RNA || rm_RTN);
            else
                assert (rm_RNE || rm_RNA || rm_RTP);

        // test rounding
        if (round_p_001)
            casez (rm)
                5'bzzzz1 /* RNE */: assert (o_unsigned == rounded_000);
                5'bzzz10 /* RNA */: assert (o_unsigned == rounded_010);
                5'bzz100 /* RTP */: assert (o_unsigned == rounded_010);
                5'bz1000 /* RTN */: assert (o_unsigned == rounded_000);
                5'b10000 /* RTZ */: assert (o_unsigned == rounded_000);
            endcase
        if (round_p_011)
            casez (rm)
                5'bzzzz1 /* RNE */: assert (o_unsigned == rounded_100);
                5'bzzz10 /* RNA */: assert (o_unsigned == rounded_100);
                5'bzz100 /* RTP */: assert (o_unsigned == rounded_100);
                5'bz1000 /* RTN */: assert (o_unsigned == rounded_010);
                5'b10000 /* RTZ */: assert (o_unsigned == rounded_010);
            endcase
        if (round_n_001)
            casez (rm)
                5'bzzzz1 /* RNE */: assert (o_unsigned == rounded_000);
                5'bzzz10 /* RNA */: assert (o_unsigned == rounded_010);
                5'bzz100 /* RTP */: assert (o_unsigned == rounded_000);
                5'bz1000 /* RTN */: assert (o_unsigned == rounded_010);
                5'b10000 /* RTZ */: assert (o_unsigned == rounded_000);
            endcase
        if (round_n_011)
            casez (rm)
                5'bzzzz1 /* RNE */: assert (o_unsigned == rounded_100);
                5'bzzz10 /* RNA */: assert (o_unsigned == rounded_100);
                5'bzz100 /* RTP */: assert (o_unsigned == rounded_010);
                5'bz1000 /* RTN */: assert (o_unsigned == rounded_100);
                5'b10000 /* RTZ */: assert (o_unsigned == rounded_010);
            endcase

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
        end
        // if multiplication overflows, addition can bring it back in range
        if (a == 32'hc3800001 && b == 32'h7b800000 && !c_special) begin
            if (c_sign)
                // result is negative, so a negative addend can't
                assert (OF);
            else if (c_exp <= 8'he7)
                // addend can't be too small
                assert (OF);
            else if (c_exp == 8'he8 && c_muladd_turning)
                // this is just the turning point for this particular value
                assert (OF);
            else
                // a large enough positive addend will never overflow (but is
                // still likely to be inexact)
                assert (!OF);
        end
`endif

`ifdef SQRTS
        assume (b_zero);
        assume (c_zero);
        assert (!UF);
        assert (!OF);
        // complex roots are invalid
        if (a_sign) begin
            if (a_norm || a_subnorm)
                assert (NV);
        end else begin
            // root exponents for normal numbers are trivial
            if (a_norm) begin
                // root of a normal is always normal
                assert (o_norm);
                if (rm_RTZ)
                    assert (o_sexp == half_a_sexp);
                else
                    assert (o_sexp == half_a_sexp || o_sexp == (half_a_sexp + 1));
    `ifdef ALTSQRT
                if (o_sexp == half_a_sexp) begin
                    if (NX) begin
                        assert (a_sig[0] == 1'b1);
                        if (rm_RTZ || rm_RTN) begin
                            assert (o_sig[22] == 1'b1);
                            assert (o_sig[21:0] == a_sig >> 1);
                        end else begin
                            assert (o_sig[22] != &a_sig);
                            if (rm_RNE && a_sig[1] == 1'b0) begin
                                assert (o_sig[21:0] == a_sig >> 1);
                            end else begin
                                assert (o_sig[21:0] == (a_sig[22:1]+1'b1));
                            end
                        end
                    end else begin
                        assert (a_sig[0] == 1'b0);
                        assert (o_sig[22] == a_sig[0]);
                        assert (o_sig[21:0] == a_sig >> 1);
                    end
                end
    `endif
            end else if (a_subnorm) begin
                // root of a subnormal is either normal or an exact subnormal
                assert (o_norm || !NX);
            end
        end
`endif
    end

`ifdef EDGE_EVENTS
    reg skip = 1;
    always @(posedge clk) begin
        if (skip) begin
            skip <= 0;
        end else begin
            // same input, different rounding mode
            if ($stable(a) && $stable(b) && $stable(c)) begin
                // general rounding
                cover (NX && rm_RNE && o_sig[1:0] == 2'b00);
                cover (NX && rm_RNE && o_sig[1:0] == 2'b10);
                if (NX && $fell(rm_RNE)) begin
                    if ($past(o_sig[1:0]) == 2'b00) begin // should be rounding from 001
                        if (o_sign) begin
`ifndef SQRTS
                            cover ($rose(rm_RNA) && o_sig[1:0] == 2'b01);
                            cover ($rose(rm_RTP) && o_sig[1:0] == 2'b00);
                            cover ($rose(rm_RTN) && o_sig[1:0] == 2'b01);
                            cover ($rose(rm_RTZ) && o_sig[1:0] == 2'b00);
`endif
                        end else begin
                            cover ($rose(rm_RNA) && o_sig[1:0] == 2'b01);
                            cover ($rose(rm_RTP) && o_sig[1:0] == 2'b01);
                            cover ($rose(rm_RTN) && o_sig[1:0] == 2'b00);
                            cover ($rose(rm_RTZ) && o_sig[1:0] == 2'b00);
                        end
                    end else if ($past(o_sig[1:0]) == 2'b10) begin // should be rounding from 011
                        if (o_sign) begin
`ifndef SQRTS
                            cover ($rose(rm_RNA) && o_sig[1:0] == 2'b10);
                            cover ($rose(rm_RTP) && o_sig[1:0] == 2'b01);
                            cover ($rose(rm_RTN) && o_sig[1:0] == 2'b10);
                            cover ($rose(rm_RTZ) && o_sig[1:0] == 2'b01);
`endif
                        end else begin
                            cover ($rose(rm_RNA) && o_sig[1:0] == 2'b10);
                            cover ($rose(rm_RTP) && o_sig[1:0] == 2'b10);
                            cover ($rose(rm_RTN) && o_sig[1:0] == 2'b01);
                            cover ($rose(rm_RTZ) && o_sig[1:0] == 2'b01);
                        end
                    end
                end

`ifndef SQRTS
// none of these are applicable for sqrt since we can't underflow or overflow
                // inf edge cases
                cover ($rose(o_inf));
                if ($rose(o_inf)) begin
                    cover ($rose(rm_RNE));
                    cover ($rose(rm_RNA));
                    cover ($rose(rm_RTN));
                    cover ($rose(rm_RTP));
                    // rm_RTZ can never round to inf
                end

    `ifndef ADDSUB
    // these aren't applicable to addsub since we they rely on underflow
                // ebmin edge cases
                cover ($rose(o_ebmin));
                if ($rose(o_ebmin)) begin
                    cover ($rose(rm_RNE));
                    cover ($rose(rm_RNA));
                    cover ($rose(rm_RTN));
                    cover ($rose(rm_RTP));
                    cover ($rose(rm_RTZ));
                end

                // zero edge cases
                cover ($rose(o_zero));
                if ($rose(o_zero)) begin
                    cover ($rose(rm_RNE));
                    cover ($rose(rm_RNA));
                    cover ($rose(rm_RTN));
                    cover ($rose(rm_RTP));
                    cover ($rose(rm_RTZ));
                end
    `endif

    `ifndef DIV
                cover ($rose(OF));
    `endif
    `ifdef TININESS_AFTER
                cover ($rose(UF));
    `endif
`endif
`ifdef MULADD
            // same multiplier output, different addend
            end else if ($stable(a) && $stable(b) && $stable(rm)) begin
                // we can get boundary cases
                cover ($rose(o_inf));
                cover ($rose(o_ebmin));
                cover ($rose(o_zero));

                // multiplication with an exception can be recovered by addend
                if ($fell(c_zero)) begin
                    cover ($fell(OF));
                    cover ($fell(UF));
                    cover ($fell(NX));
                    // unless it was an invalid multiplication
                    if ($past(NV))
                        assert (NV);
                end

                // flags are always determined after addition
                cover ($rose(OF));
                cover ($rose(UF));
                cover ($rose(NV));
                cover ($rose(NX));
`endif
            end
        end
    end
`endif
endmodule
