if (NOT YOSYS_ENABLE_VERIFIC)
	# Stub interface library.
	add_library(verific INTERFACE)
	set(verific_data_files)
elseif (NOT TARGET verific)
	if (NOT YOSYS_VERIFIC_COMPONENTS)
		get_verific_components(YOSYS_VERIFIC_COMPONENTS)
	endif()

	if (NOT YOSYS_VERIFIC_FEATURES)
		foreach (component ${YOSYS_VERIFIC_COMPONENTS})
			if (component MATCHES "^(hier_tree|vhdl|edif|extensions)$")
				list(APPEND YOSYS_VERIFIC_FEATURES ${component})
			elseif (component STREQUAL "verilog")
				list(APPEND YOSYS_VERIFIC_FEATURES systemverilog)
			elseif (component STREQUAL "synlib")
				list(APPEND YOSYS_VERIFIC_FEATURES liberty)
			endif()
		endforeach()
	endif()

	message(STATUS "Verific library components: ${YOSYS_VERIFIC_COMPONENTS}")
	message(STATUS "Verific frontend features: ${YOSYS_VERIFIC_FEATURES}")

	get_verific_options(verific_include_dirs verific_libraries ${YOSYS_VERIFIC_COMPONENTS})
	add_library(verific INTERFACE)
	target_include_directories(verific INTERFACE
		${verific_include_dirs}
	)
	target_link_libraries(verific INTERFACE
		$<LINK_LIBRARY:WHOLE_ARCHIVE,${verific_libraries}>
		PkgConfig::zlib
	)

	set(verific_data_files)
	if ("vhdl" IN_LIST YOSYS_VERIFIC_FEATURES)
		foreach (vdb_std 1987 1993 2008 2019)
			set(vdb_std_root ${YOSYS_VERIFIC_DIR}/vhdl_packages/vdbs_${vdb_std})
			file(GLOB_RECURSE vdb_files RELATIVE ${vdb_std_root} ${vdb_std_root}/*)
			foreach (vdb_file ${vdb_files})
				list(APPEND verific_data_files
					verific/vhdl_vdbs_${vdb_std}/${vdb_file}
					${YOSYS_VERIFIC_DIR}/vhdl_packages/vdbs_${vdb_std}/${vdb_file}
				)
			endforeach()
		endforeach()
	endif()
endif()

yosys_frontend(verific
	verific.cc
	verific.h
	$<${YOSYS_ENABLE_VERIFIC}:verificsva.cc>
	DEFINITIONS
		$<$<IN_LIST:hier_tree,${YOSYS_VERIFIC_FEATURES}>:VERIFIC_HIER_TREE_SUPPORT>
		$<$<IN_LIST:systemverilog,${YOSYS_VERIFIC_FEATURES}>:VERIFIC_SYSTEMVERILOG_SUPPORT>
		$<$<IN_LIST:vhdl,${YOSYS_VERIFIC_FEATURES}>:VERIFIC_VHDL_SUPPORT>
		$<$<IN_LIST:edif,${YOSYS_VERIFIC_FEATURES}>:VERIFIC_EDIF_SUPPORT>
		$<$<IN_LIST:liberty,${YOSYS_VERIFIC_FEATURES}>:VERIFIC_LIBERTY_SUPPORT>
		$<$<IN_LIST:extensions,${YOSYS_VERIFIC_FEATURES}>:YOSYSHQ_VERIFIC_EXTENSIONS>
		$<${ENABLE_VERIFIC_SILIMATE_EXTENSIONS}:SILIMATE_VERIFIC_EXTENSIONS>
	LIBRARIES
		verific
	REQUIRES
		sha1
		read_verilog
	PROVIDES
		read
	DATA_EXPLICIT
		${verific_data_files}
)
