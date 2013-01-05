#!/bin/bash
if [ -n "$REMOTE_YOSYS_ROOT" ]; then
	rsync --exclude=".svn" --exclude="*.log" -rv -e "${REMOTE_YOSYS_SSH:-ssh} -C" "$REMOTE_YOSYS_ROOT"/tests/or1200/. .
fi
fm_shell -64 -file run-fm.do 2>&1 | tee run-fm.log
