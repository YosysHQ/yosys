yosys_core(fsmdata INTERFACE
	fsmdata.h
	DATA_DIR
		include/passes/fsm
	DATA_FILES
		fsmdata.h
)

function(yosys_fsm_pass)
  yosys_pass(${ARGV} REQUIRES fsmdata)
endfunction()

yosys_fsm_pass(fsm_detect
	fsm_detect.cc
)
yosys_fsm_pass(fsm_extract
	fsm_extract.cc
)
yosys_fsm_pass(fsm_opt
	fsm_opt.cc
)
yosys_fsm_pass(fsm_expand
	fsm_expand.cc
	REQUIRES
		fsm_opt
)
yosys_fsm_pass(fsm_recode
	fsm_recode.cc
)
yosys_fsm_pass(fsm_info
	fsm_info.cc
)
yosys_fsm_pass(fsm_export
	fsm_export.cc
)
yosys_fsm_pass(fsm_map
	fsm_map.cc
)

yosys_pass(fsm
	fsm.cc
	REQUIRES
		fsm_detect
		fsm_expand
		fsm_export
		fsm_extract
		fsm_info
		fsm_map
		fsm_opt
		fsm_recode
		opt_clean
)
