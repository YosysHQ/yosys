#!/bin/bash

fast_mode=false
update_mode=false

set -- $(getopt fu "$@")
while [ $# -gt 0 ]; do
	case "$1" in
		-f)
			fast_mode=true
			;;
		-u)
			update_mode=true
			;;
		--)
			shift
			break
			;;
		-*)
			echo "$0: error - unrecognized option $1" 1>&2
			exit 1
			;;
		*)
			break
	esac
	shift
done

PDFTEX_OPT="-shell-escape -halt-on-error"

if $update_mode; then
	make -C ..
	../yosys -p 'help -write-tex-command-reference-manual'
fi

if ! $fast_mode; then
	md5sum *.aux *.bbl *.blg > autoloop.old
fi

set -ex

pdflatex $PDFTEX_OPT manual.tex

if ! $fast_mode; then
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
fi

