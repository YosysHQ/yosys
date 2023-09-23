GIT_METADATA_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

# Note: We arrange for .gitcommit to contain the (short) commit hash in
# tarballs generated with git-archive(1) using .gitattributes. The git repo
# will have this file in its unexpanded form tough, in which case we fall
# back to calling git directly.

TARBALL_GIT_REV := $(shell cat $(GIT_METADATA_DIR)/.gitcommit)
ifeq ($(TARBALL_GIT_REV),$$Format:%h$$)
GIT_REV := $(shell GIT_DIR=$(GIT_METADATA_DIR)/.git git rev-parse --short=9 HEAD || echo UNKNOWN)
GIT_EPOCH = $(shell GIT_DIR=$(GIT_METADATA_DIR)/.git git show --format=%ct -q || echo 1640991600)
#^ 1640991600 == 2022-01-01 00:00:00
else
GIT_REV := $(TARBALL_GIT_REV)
GIT_EPOCH = $(shell cat $(GIT_METADATA_DIR)/.gitepoch)
endif
