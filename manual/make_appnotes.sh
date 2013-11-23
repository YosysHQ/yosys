#!/bin/bash

set -ex
for job in APPNOTE_010_Verilog_to_BLIF
do
	[ -f $job.ok -a $job.ok -nt $job.tex ] && continue
	old_md5=$([ -f $job.aux ] && md5sum < $job.aux)
	while
		pdflatex -shell-escape -halt-on-error $job.tex
		new_md5=$(md5sum < $job.aux)
		[ "$old_md5" != "$new_md5" ]
	do
		old_md5="$new_md5"
	done
	touch $job.ok
done

