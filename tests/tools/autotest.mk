
# Don't bother defining default values for SEED and EXTRA_FLAGS.
# Their "natural" default values should be sufficient,
#   and they may be overridden in the environment.
ifneq ($(strip $(SEED)),)
SEEDOPT=-S$(SEED)
endif

$(MAKECMDGOALS):
	@$(basename $(MAKEFILE_LIST)).sh -G -j $(SEEDOPT) $(EXTRA_FLAGS) $@

.PHONY: $(MAKECMDGOALS)

