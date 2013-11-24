#!/bin/sed -r
/^(wire|assign|reg|event)/ d;
/^(genvar|generate|always|initial)/,/^end/ d;
s/ reg / /;
