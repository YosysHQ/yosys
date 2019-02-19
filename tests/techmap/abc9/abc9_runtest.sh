#!/bin/bash

set -ev

../../../yosys -p 'abc9 -lut 4; check; select -assert-count 2 t:$lut; select -assert-none c:* t:$lut %n %i' abc9.v
