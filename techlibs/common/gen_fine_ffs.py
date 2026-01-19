TEMPLATES = [
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_SR_{S:N|P}{R:N|P}_ (S, R, Q)
//* group reg_latch
//-
//- A set-reset latch with {S:negative|positive} polarity SET and {R:negative|positive} polarity RESET.
//-
//- Truth table:    S R | Q
//-                -----+---
//-                 - {R:0|1} | 0
//-                 {S:0|1} - | 1
//-                 - - | q
//-
module \$_SR_{S:N|P}{R:N|P}_ (S, R, Q);
input S, R;
output reg Q;
always @* begin
	if (R == {R:0|1})
		Q <= 0;
	else if (S == {S:0|1})
		Q <= 1;
end
endmodule
""",
"""
`ifdef SIMCELLS_FF
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_FF_ (D, Q)
//* group reg_ff
//-
//- A D-type flip-flop that is clocked from the implicit global clock. (This cell
//- type is usually only used in netlists for formal verification.)
//-
module \$_FF_ (D, Q);
input D;
output reg Q;
always @($global_clock) begin
	Q <= D;
end
endmodule
`endif
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DFF_{C:N|P}_ (D, C, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop.
//-
//- Truth table:    D C | Q
//-                -----+---
//-                 d {C:\\|/} | d
//-                 - - | q
//-
module \$_DFF_{C:N|P}_ (D, C, Q);
input D, C;
output reg Q;
always @({C:neg|pos}edge C) begin
	Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DFFE_{C:N|P}{E:N|P}_ (D, C, E, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {E:negative|positive} polarity enable.
//-
//- Truth table:    D C E | Q
//-                -------+---
//-                 d {C:\\|/} {E:0|1} | d
//-                 - - - | q
//-
module \$_DFFE_{C:N|P}{E:N|P}_ (D, C, E, Q);
input D, C, E;
output reg Q;
always @({C:neg|pos}edge C) begin
	if ({E:!E|E}) Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DFF_{C:N|P}{R:N|P}{V:0|1}_ (D, C, R, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {R:negative|positive} polarity {V:reset|set}.
//-
//- Truth table:    D C R | Q
//-                -------+---
//-                 - - {R:0|1} | {V:0|1}
//-                 d {C:\\|/} - | d
//-                 - - - | q
//-
module \$_DFF_{C:N|P}{R:N|P}{V:0|1}_ (D, C, R, Q);
input D, C, R;
output reg Q;
always @({C:neg|pos}edge C or {R:neg|pos}edge R) begin
	if (R == {R:0|1})
		Q <= {V:0|1};
	else
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DFFE_{C:N|P}{R:N|P}{V:0|1}{E:N|P}_ (D, C, R, E, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {R:negative|positive} polarity {V:reset|set} and {E:negative|positive}
//- polarity clock enable.
//-
//- Truth table:    D C R E | Q
//-                ---------+---
//-                 - - {R:0|1} - | {V:0|1}
//-                 d {C:\\|/} - {E:0|1} | d
//-                 - - - - | q
//-
module \$_DFFE_{C:N|P}{R:N|P}{V:0|1}{E:N|P}_ (D, C, R, E, Q);
input D, C, R, E;
output reg Q;
always @({C:neg|pos}edge C or {R:neg|pos}edge R) begin
	if (R == {R:0|1})
		Q <= {V:0|1};
	else if (E == {E:0|1})
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_ALDFF_{C:N|P}{L:N|P}_ (D, C, L, AD, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {L:negative|positive} polarity async load.
//-
//- Truth table:    D C L AD | Q
//-                ----------+---
//-                 - - {L:0|1} a  | a
//-                 d {C:\\|/} - -  | d
//-                 - - - -  | q
//-
module \$_ALDFF_{C:N|P}{L:N|P}_ (D, C, L, AD, Q);
input D, C, L, AD;
output reg Q;
always @({C:neg|pos}edge C or {L:neg|pos}edge L) begin
	if (L == {L:0|1})
		Q <= AD;
	else
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_ALDFFE_{C:N|P}{L:N|P}{E:N|P}_ (D, C, L, AD, E, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {L:negative|positive} polarity async load and {E:negative|positive}
//- polarity clock enable.
//-
//- Truth table:    D C L AD E | Q
//-                ------------+---
//-                 - - {L:0|1} a  - | a
//-                 d {C:\\|/} - -  {E:0|1} | d
//-                 - - - -  - | q
//-
module \$_ALDFFE_{C:N|P}{L:N|P}{E:N|P}_ (D, C, L, AD, E, Q);
input D, C, L, AD, E;
output reg Q;
always @({C:neg|pos}edge C or {L:neg|pos}edge L) begin
	if (L == {L:0|1})
		Q <= AD;
	else if (E == {E:0|1})
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DFFSR_{C:N|P}{S:N|P}{R:N|P}_ (C, S, R, D, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {S:negative|positive} polarity set and {R:negative|positive}
//- polarity reset.
//-
//- Truth table:    C S R D | Q
//-                ---------+---
//-                 - - {R:0|1} - | 0
//-                 - {S:0|1} - - | 1
//-                 {C:\\|/} - - d | d
//-                 - - - - | q
//-
module \$_DFFSR_{C:N|P}{S:N|P}{R:N|P}_ (C, S, R, D, Q);
input C, S, R, D;
output reg Q;
always @({C:neg|pos}edge C, {S:neg|pos}edge S, {R:neg|pos}edge R) begin
	if (R == {R:0|1})
		Q <= 0;
	else if (S == {S:0|1})
		Q <= 1;
	else
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DFFSRE_{C:N|P}{S:N|P}{R:N|P}{E:N|P}_ (C, S, R, E, D, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {S:negative|positive} polarity set, {R:negative|positive}
//- polarity reset and {E:negative|positive} polarity clock enable.
//-
//- Truth table:    C S R E D | Q
//-                -----------+---
//-                 - - {R:0|1} - - | 0
//-                 - {S:0|1} - - - | 1
//-                 {C:\\|/} - - {E:0|1} d | d
//-                 - - - - - | q
//-
module \$_DFFSRE_{C:N|P}{S:N|P}{R:N|P}{E:N|P}_ (C, S, R, E, D, Q);
input C, S, R, E, D;
output reg Q;
always @({C:neg|pos}edge C, {S:neg|pos}edge S, {R:neg|pos}edge R) begin
	if (R == {R:0|1})
		Q <= 0;
	else if (S == {S:0|1})
		Q <= 1;
        else if (E == {E:0|1})
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_SDFF_{C:N|P}{R:N|P}{V:0|1}_ (D, C, R, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {R:negative|positive} polarity synchronous {V:reset|set}.
//-
//- Truth table:    D C R | Q
//-                -------+---
//-                 - {C:\\|/} {R:0|1} | {V:0|1}
//-                 d {C:\\|/} - | d
//-                 - - - | q
//-
module \$_SDFF_{C:N|P}{R:N|P}{V:0|1}_ (D, C, R, Q);
input D, C, R;
output reg Q;
always @({C:neg|pos}edge C) begin
	if (R == {R:0|1})
		Q <= {V:0|1};
	else
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_SDFFE_{C:N|P}{R:N|P}{V:0|1}{E:N|P}_ (D, C, R, E, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {R:negative|positive} polarity synchronous {V:reset|set} and {E:negative|positive}
//- polarity clock enable (with {V:reset|set} having priority).
//-
//- Truth table:    D C R E | Q
//-                ---------+---
//-                 - {C:\\|/} {R:0|1} - | {V:0|1}
//-                 d {C:\\|/} - {E:0|1} | d
//-                 - - - - | q
//-
module \$_SDFFE_{C:N|P}{R:N|P}{V:0|1}{E:N|P}_ (D, C, R, E, Q);
input D, C, R, E;
output reg Q;
always @({C:neg|pos}edge C) begin
	if (R == {R:0|1})
		Q <= {V:0|1};
	else if (E == {E:0|1})
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_SDFFCE_{C:N|P}{R:N|P}{V:0|1}{E:N|P}_ (D, C, R, E, Q)
//* group reg_ff
//-
//- A {C:negative|positive} edge D-type flip-flop with {R:negative|positive} polarity synchronous {V:reset|set} and {E:negative|positive}
//- polarity clock enable (with clock enable having priority).
//-
//- Truth table:    D C R E | Q
//-                ---------+---
//-                 - {C:\\|/} {R:0|1} {E:0|1} | {V:0|1}
//-                 d {C:\\|/} - {E:0|1} | d
//-                 - - - - | q
//-
module \$_SDFFCE_{C:N|P}{R:N|P}{V:0|1}{E:N|P}_ (D, C, R, E, Q);
input D, C, R, E;
output reg Q;
always @({C:neg|pos}edge C) begin
	if (E == {E:0|1}) begin
		if (R == {R:0|1})
			Q <= {V:0|1};
		else
			Q <= D;
	end
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DLATCH_{E:N|P}_ (E, D, Q)
//* group reg_latch
//-
//- A {E:negative|positive} enable D-type latch.
//-
//- Truth table:    E D | Q
//-                -----+---
//-                 {E:0|1} d | d
//-                 - - | q
//-
module \$_DLATCH_{E:N|P}_ (E, D, Q);
input E, D;
output reg Q;
always @* begin
	if (E == {E:0|1})
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DLATCH_{E:N|P}{R:N|P}{V:0|1}_ (E, R, D, Q)
//* group reg_latch
//-
//- A {E:negative|positive} enable D-type latch with {R:negative|positive} polarity {V:reset|set}.
//-
//- Truth table:    E R D | Q
//-                -------+---
//-                 - {R:0|1} - | {V:0|1}
//-                 {E:0|1} - d | d
//-                 - - - | q
//-
module \$_DLATCH_{E:N|P}{R:N|P}{V:0|1}_ (E, R, D, Q);
input E, R, D;
output reg Q;
always @* begin
	if (R == {R:0|1})
                Q <= {V:0|1};
	else if (E == {E:0|1})
		Q <= D;
end
endmodule
""",
"""
//  |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
//-
//-     $_DLATCHSR_{E:N|P}{S:N|P}{R:N|P}_ (E, S, R, D, Q)
//* group reg_latch
//-
//- A {E:negative|positive} enable D-type latch with {S:negative|positive} polarity set and {R:negative|positive}
//- polarity reset.
//-
//- Truth table:    E S R D | Q
//-                ---------+---
//-                 - - {R:0|1} - | 0
//-                 - {S:0|1} - - | 1
//-                 {E:0|1} - - d | d
//-                 - - - - | q
//-
module \$_DLATCHSR_{E:N|P}{S:N|P}{R:N|P}_ (E, S, R, D, Q);
input E, S, R, D;
output reg Q;
always @* begin
	if (R == {R:0|1})
		Q <= 0;
	else if (S == {S:0|1})
		Q <= 1;
	else if (E == {E:0|1})
		Q <= D;
end
endmodule
""",
]

lines = []
with open('simcells.v') as f:
    for l in f:
        lines.append(l)
        if 'START AUTOGENERATED CELL TYPES' in l:
            break

with open('simcells.v', 'w') as f:
    for l in lines:
        f.write(l)
    for template in TEMPLATES:
        chunks = []
        vars = {}
        pos = 0
        while pos < len(template):
            if template[pos] != '{':
                np = template.find('{', pos)
                if np == -1:
                    np = len(template)
                chunks.append(template[pos:np])
                pos = np
            else:
                np = template.index('}', pos)
                sub = template[pos + 1:np]
                pos = np + 1
                var, _, vals = sub.partition(':')
                if not vals:
                    raise ValueError(sub)
                vals = vals.split('|')
                if var not in vars:
                    vars[var] = len(vals)
                else:
                    if vars[var] != len(vals):
                        raise ValueError(vars[var], vals)
                chunks.append((var, vals))
        combs = [{}]
        for var in vars:
            combs = [
                {
                    var: i,
                    **comb,
                }
                for comb in combs
                for i in range(vars[var])
            ]
        for comb in combs:
            f.write(
                ''.join(
                    c if isinstance(c, str) else c[1][comb[c[0]]]
                    for c in chunks
                )
            )
