#!/bin/bash
for f in $( find . -name .gitignore ); do sed -Ee "s,^,find ${f%.gitignore} -name ',; s,$,' | xargs rm -f,;" $f; done | bash -v
