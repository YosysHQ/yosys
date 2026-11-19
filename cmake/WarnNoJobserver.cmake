if (NOT "$ENV{MAKEFLAGS}" MATCHES "(^| )(-j|--jobs)")
	message(WARNING
		"The ${GENERATOR} generator doesn't share its job slots with the nested make, "
		"so it will run one job at a time. Set MAKEFLAGS=-j<N> in the environment, "
		"or build with a Makefile generator.")
endif()
