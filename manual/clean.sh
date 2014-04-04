#!/bin/bash
for f in $( find . -name .gitignore ); do sed -re "s,^,find ${f%.gitignore} -name ',; s,$,' | xargs -r rm -f,;" $f; done | bash -v
