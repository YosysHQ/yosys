#!/bin/bash

fast_mode=false

set -- $(getopt fu "$@")
while [ $# -gt 0 ]; do
	case "$1" in
		-f)
			fast_mode=true
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

set -ex

if ! $fast_mode; then
	! md5sum *.aux *.snm *.nav *.toc > autoloop.old
	make -C PRESENTATION_Intro
	make -C PRESENTATION_ExSyn
	make -C PRESENTATION_ExAdv
	make -C PRESENTATION_ExOth
	make -C PRESENTATION_Prog
fi

set -ex

pdflatex $PDFTEX_OPT presentation.tex

if ! $fast_mode; then
	while
		md5sum *.aux *.snm *.nav *.toc > autoloop.new
		! cmp autoloop.old autoloop.new
	do
		cp autoloop.new autoloop.old
		pdflatex $PDFTEX_OPT presentation.tex
	done

	rm -f autoloop.old
	rm -f autoloop.new
fi

