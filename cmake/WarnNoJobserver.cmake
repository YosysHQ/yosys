if (NOT "$ENV{MAKEFLAGS}" MATCHES "(^| )(-j|--jobs)")
	message(WARNING
		"${GENERATOR} doesn't pass job tokens to make, so make runs one job at a time. "
		"Set MAKEFLAGS=-j<N> or use the Unix Makefiles generator.")
endif()
