if (YOSYS_ENABLE_VERIFIC)
	# user-facing options
	option(WITH_VERIFIC_SYSTEMVERILOG "Enable Verific SystemVerilog support" ON)
	option(WITH_VERIFIC_VHDL "Enable Verific VHDL support" ON)
	option(WITH_VERIFIC_HIER_TREE "Enable Verific hier_tree component" ON)
	option(WITH_VERIFIC_SILIMATE_EXTENSIONS "Enable Silimate-specific Verific modifications" ON)
	option(WITH_VERIFIC_YOSYSHQ_EXTENSIONS "Enable YosysHQ-specific Verific modifications" OFF)
	option(WITH_VERIFIC_EDIF "Enable Verific EDIF support" OFF)
	option(WITH_VERIFIC_LIBERTY "Enable Verific Liberty file support" OFF)
	option(WITH_VERIFIC_UPF "Enable Verific UPF support (requires Tcl support)" OFF)

	# further checks and conditions
	condition(ENABLE_VERIFIC_SYSTEMVERILOG WITH_VERIFIC_SYSTEMVERILOG)
	condition(ENABLE_VERIFIC_VHDL WITH_VERIFIC_VHDL)
	condition(ENABLE_VERIFIC_HIER_TREE WITH_VERIFIC_HIER_TREE)
	condition(ENABLE_VERIFIC_SILIMATE_EXTENSIONS WITH_VERIFIC_SILIMATE_EXTENSIONS)
	condition(ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS WITH_VERIFIC_YOSYSHQ_EXTENSIONS)
	condition(ENABLE_VERIFIC_EDIF WITH_VERIFIC_EDIF)
	condition(ENABLE_VERIFIC_LIBERTY WITH_VERIFIC_LIBERTY)
	condition(ENABLE_VERIFIC_UPF WITH_VERIFIC_UPF AND YOSYS_ENABLE_TCL)

	# construct component list
	list(APPEND YOSYS_VERIFIC_COMPONENTS database util containers pct)
	if (ENABLE_VERIFIC_HIER_TREE)
		list(APPEND YOSYS_VERIFIC_COMPONENTS hier_tree)
	endif()
	if (ENABLE_VERIFIC_SYSTEMVERILOG)
		list(APPEND YOSYS_VERIFIC_COMPONENTS verilog)
	endif()
	if (ENABLE_VERIFIC_VHDL)
		list(APPEND YOSYS_VERIFIC_COMPONENTS vhdl)
	endif()
	if (ENABLE_VERIFIC_EDIF)
		list(APPEND YOSYS_VERIFIC_COMPONENTS edif)
	endif()
	if (ENABLE_VERIFIC_LIBERTY)
		list(APPEND YOSYS_VERIFIC_COMPONENTS synlib)
	endif()
	if (ENABLE_VERIFIC_UPF)
		list(APPEND YOSYS_VERIFIC_COMPONENTS hdl_file_sort verilog_nl commands upf)
	endif()
	if (ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS)
		list(APPEND YOSYS_VERIFIC_COMPONENTS extensions)
	endif()

	# Prepare Silimate-specific objects overriding existing Verific symbols
	flex_target(veri_flex
		${YOSYS_VERIFIC_DIR}/verilog/verilog.l
		veri_lex.cpp
		COMPILE_FLAGS "--prefix=veri --noline"
	)
	bison_target(veri_yacc
		${YOSYS_VERIFIC_DIR}/verilog/verilog.y
		veri_yacc.cpp
		DEFINES_FILE veri_yacc.h
		COMPILE_FLAGS "--name-prefix=veri --no-lines"
	)

	string(REPLACE ".a" ".raw.a" VERIFIC_RAW_LIB_SUFFIX "${VERIFIC_LIB_SUFFIX}")

	# prepare archive list
	foreach(component ${YOSYS_VERIFIC_COMPONENTS})
		if (component STREQUAL "util")
			list(APPEND VERIFIC_OBJECTS ${YOSYS_VERIFIC_DIR}/${component}/util${VERIFIC_RAW_LIB_SUFFIX})
		elseif (component STREQUAL "database")
			list(APPEND VERIFIC_OBJECTS ${YOSYS_VERIFIC_DIR}/${component}/database${VERIFIC_RAW_LIB_SUFFIX})
		elseif (component STREQUAL "verilog")
			list(APPEND VERIFIC_OBJECTS ${YOSYS_VERIFIC_DIR}/${component}/verilog${VERIFIC_RAW_LIB_SUFFIX})
		else()
			list(APPEND VERIFIC_OBJECTS ${YOSYS_VERIFIC_DIR}/${component}/${component}${VERIFIC_LIB_SUFFIX})
		endif()
	endforeach()

	# Compile "verific_merged", which prioritizes the custom, listed Silimate
	# files but also merges in .a files from upstream with a lower priority.
	add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/empty.cpp
		COMMAND touch ${CMAKE_CURRENT_BINARY_DIR}/empty.cpp
	)
	add_library(verific_merged STATIC
		${CMAKE_CURRENT_BINARY_DIR}/empty.cpp # empty file so the source list isn't empty if silimate extensions are off
		$<${ENABLE_VERIFIC_SILIMATE_EXTENSIONS}:veri_yacc.cpp>
		$<${ENABLE_VERIFIC_SILIMATE_EXTENSIONS}:veri_lex.cpp>
		$<${ENABLE_VERIFIC_SILIMATE_EXTENSIONS}:${YOSYS_VERIFIC_DIR}/util/UtilSilimate.cpp>
		$<${ENABLE_VERIFIC_SILIMATE_EXTENSIONS}:${YOSYS_VERIFIC_DIR}/database/DBSilimate.cpp>
		$<${ENABLE_VERIFIC_SILIMATE_EXTENSIONS}:${YOSYS_VERIFIC_DIR}/verilog/VeriSilimate.cpp>
	)
	target_include_directories(verific_merged PRIVATE
		${YOSYS_VERIFIC_DIR}/containers
		${YOSYS_VERIFIC_DIR}/database
		${YOSYS_VERIFIC_DIR}/util
		${YOSYS_VERIFIC_DIR}/hier_tree
		${YOSYS_VERIFIC_DIR}/vhdl
		${YOSYS_VERIFIC_DIR}/verilog
	)
	add_custom_command(TARGET verific_merged POST_BUILD
		DEPENDS
			${VERIFIC_OBJECTS}
		COMMAND
			env CMAKE_OBJCOPY=${CMAKE_OBJCOPY} ${Python3_EXECUTABLE} ${CMAKE_CURRENT_LIST_DIR}/SilimateVerific-merge-archive.py $<TARGET_FILE:verific_merged> ${VERIFIC_OBJECTS}
	)

	# Prepare verific interface library as in YosysVerific.cmake
	get_verific_options(verific_include_dirs verific_libraries ${YOSYS_VERIFIC_COMPONENTS})
	target_include_directories(verific INTERFACE
		${verific_include_dirs}
	)
	target_link_libraries(verific INTERFACE
		$<LINK_LIBRARY:WHOLE_ARCHIVE,$<TARGET_FILE:verific_merged>>
		PkgConfig::zlib
	)

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
