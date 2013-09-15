#!/bin/sed -r
/^(wire|assign|reg)/ d;
/^(genvar|always|initial)/,/^end/ d;
s/ reg / /;
