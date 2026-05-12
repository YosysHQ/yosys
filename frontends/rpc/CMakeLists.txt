yosys_frontend(rpc
	rpc_frontend.cc
	REQUIRES
		json11
		sha1
	ENABLE_IF
		YOSYS_ENABLE_SPAWN
)
