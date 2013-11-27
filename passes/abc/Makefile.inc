
ifeq ($(ENABLE_ABC),1)
OBJS += passes/abc/abc.o
OBJS += passes/abc/vlparse.o
OBJS += passes/abc/blifparse.o
endif

