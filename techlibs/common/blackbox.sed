#!/bin/sed -r
/^(wire|assign|reg|event|integer|localparam|\/\/|[\/ ]\*| *$|`)/ d;
/^(genvar|generate|always|initial|task|function)/,/^end/ d;
/^endmodule/ s/$/\n/;
s/ reg / /;
