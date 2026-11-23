# Verify every F* module in src/ and programs/.
#
#   make                 verify everything (only re-checks what changed)
#   make check FILE=programs/LU.fst
#                        verify one file (and whatever it depends on)
#   make clean           drop cached .checked files
#
# Extra flags: make FSTAR_FLAGS="--z3rlimit_factor 2"

FSTAR_EXE   ?= fstar.exe
CACHE_DIR   := .cache
SRC_FILES   := $(wildcard src/*.fst programs/*.fst)

FSTAR = $(FSTAR_EXE) \
  --include src --include programs \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --already_cached 'Prims FStar' \
  $(FSTAR_FLAGS)

CHECKED_FILES := $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(notdir $(SRC_FILES))))

.PHONY: all verify check clean
.DEFAULT_GOAL := all

all verify: $(CHECKED_FILES)

# Dependency graph between modules, computed by F* itself.
.depend: $(SRC_FILES) Makefile
	@$(FSTAR) --dep full $(SRC_FILES) -o $@

-include .depend

# The first prerequisite of each .checked rule in .depend is its source file.
$(CACHE_DIR)/%.checked:
	@echo "[CHECK] $<"
	@$(FSTAR) $< && touch -c $@

# `make check FILE=programs/LU.fst` checks just that file and its dependencies.
check:
	@test -n "$(FILE)" || { echo "usage: make check FILE=path/to/Module.fst"; exit 1; }
	@$(MAKE) --no-print-directory $(CACHE_DIR)/$(notdir $(FILE)).checked

clean:
	rm -rf $(CACHE_DIR) .depend
