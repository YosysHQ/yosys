#!/bin/bash

PDFTEX_OPT="-shell-escape -halt-on-error"

md5sum *.aux *.bbl *.blg > autoloop.old
set -ex

pdflatex $PDFTEX_OPT manual.tex
bibtex manual.aux
bibtex weblink.aux

while
	md5sum *.aux *.bbl *.blg > autoloop.new
	! cmp autoloop.old autoloop.new
do
	cp autoloop.new autoloop.old
	pdflatex $PDFTEX_OPT manual.tex
done

rm -f autoloop.old
rm -f autoloop.new

