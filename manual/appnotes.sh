#!/bin/bash

set -ex
for job in APPNOTE_010_Verilog_to_BLIF APPNOTE_011_Design_Investigation APPNOTE_012_Verilog_to_BTOR
do
	[ -f $job.ok -a $job.ok -nt $job.tex ] && continue
	if [ -f $job/make.sh ]; then
		cd $job
		bash make.sh
		cd ..
	fi
	old_md5=$([ -f $job.aux ] && md5sum < $job.aux || true)
	while
		pdflatex -shell-escape -halt-on-error $job.tex || exit
		new_md5=$(md5sum < $job.aux)
		[ "$old_md5" != "$new_md5" ]
	do
		old_md5="$new_md5"
	done
	touch $job.ok
done

