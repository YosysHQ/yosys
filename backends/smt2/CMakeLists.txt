yosys_backend(smt2
	smt2.cc
	REQUIRES
		json11
	DATA_DIR
		python3
	DATA_FILES
		smtio.py
		ywio.py
	REQUIRES
		bmuxmap
		demuxmap
)

yosys_python_executable(yosys-smtbmc smtbmc.py
	INSTALL_IF YOSYS_INSTALL_DRIVER OR YOSYS_INSTALL_LIBRARY
)
yosys_python_executable(yosys-witness witness.py
	INSTALL_IF YOSYS_INSTALL_DRIVER OR YOSYS_INSTALL_LIBRARY
)
