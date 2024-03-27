
OBJS += passes/techmap/flatten.o
OBJS += passes/techmap/techmap.o
OBJS += passes/techmap/simplemap.o
OBJS += passes/techmap/dfflibmap.o
OBJS += passes/techmap/maccmap.o
OBJS += passes/techmap/booth.o
OBJS += passes/techmap/libparse.o

ifeq ($(ENABLE_ABC),1)
OBJS += passes/techmap/abc.o
OBJS += passes/techmap/abc9.o
OBJS += passes/techmap/abc9_exe.o
OBJS += passes/techmap/abc9_ops.o
ifneq ($(ABCEXTERNAL),)
passes/techmap/abc.o: CXXFLAGS += -DABCEXTERNAL='"$(ABCEXTERNAL)"'
passes/techmap/abc9.o: CXXFLAGS += -DABCEXTERNAL='"$(ABCEXTERNAL)"'
passes/techmap/abc9_exe.o: CXXFLAGS += -DABCEXTERNAL='"$(ABCEXTERNAL)"'
endif
endif

ifneq ($(SMALL),1)
OBJS += passes/techmap/iopadmap.o
OBJS += passes/techmap/clkbufmap.o
OBJS += passes/techmap/hilomap.o
OBJS += passes/techmap/extract.o
OBJS += passes/techmap/extract_fa.o
OBJS += passes/techmap/extract_counter.o
OBJS += passes/techmap/extract_reduce.o
OBJS += passes/techmap/alumacc.o
OBJS += passes/techmap/dffinit.o
OBJS += passes/techmap/pmuxtree.o
OBJS += passes/techmap/bmuxmap.o
OBJS += passes/techmap/demuxmap.o
OBJS += passes/techmap/bwmuxmap.o
OBJS += passes/techmap/muxcover.o
OBJS += passes/techmap/aigmap.o
OBJS += passes/techmap/tribuf.o
OBJS += passes/techmap/lut2mux.o
OBJS += passes/techmap/nlutmap.o
OBJS += passes/techmap/shregmap.o
OBJS += passes/techmap/deminout.o
OBJS += passes/techmap/insbuf.o
OBJS += passes/techmap/attrmvcp.o
OBJS += passes/techmap/attrmap.o
OBJS += passes/techmap/zinit.o
OBJS += passes/techmap/dfflegalize.o
OBJS += passes/techmap/dffunmap.o
OBJS += passes/techmap/flowmap.o
OBJS += passes/techmap/extractinv.o
OBJS += passes/techmap/cellmatch.o
endif

ifeq ($(DISABLE_SPAWN),0)
TARGETS += $(PROGRAM_PREFIX)yosys-filterlib$(EXE)
EXTRA_OBJS += passes/techmap/filterlib.o

$(PROGRAM_PREFIX)yosys-filterlib$(EXE): passes/techmap/filterlib.o
	$(Q) mkdir -p $(dir $@)
	$(P) $(CXX) -o $(PROGRAM_PREFIX)yosys-filterlib$(EXE) $(LINKFLAGS) $^ $(LIBS)
endif
