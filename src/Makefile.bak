# === Directories ===
OUTPUT_DIR     = .output
HINT_DIR       = .hints
DEP_FILE       = .depend

# === F* Setup ===
FSTAR          ?= fstar.exe
KRML_HOME      ?= ../external-libs/karamel
HACL_HOME      ?= ../external-libs/hacl-star

ifeq (,$(FSTAR))
  $(error FSTAR is not defined)
endif

ifeq (,$(KRML_HOME))
  $(error KRML_HOME is not defined)
endif

ifeq (,$(HACL_HOME))
  $(error HACL_HOME is not defined)
endif

include $(HACL_HOME)/Makefile.include

# === File Discovery ===
FSTAR_FILES    = $(wildcard *.fst)
CHECKED_FILES  = $(addprefix $(OUTPUT_DIR)/, $(FSTAR_FILES:.fst=.checked))

# === Include Paths ===
FSTAR_INCLUDE_DIRS = \
  $(KRML_HOME)/krmllib \
  $(ALL_HACL_DIRS) \

# We need those flags to properly extract code which uses Vale
ADDITIONAL_VALE_KRML_FLAGS = \
  -library 'Vale.Stdcalls.*' \
  -no-prefix 'Vale.Stdcalls.*' \
  -static-header 'Vale.Inline.*' \
  -library 'Vale.Inline.X64.Fadd_inline' \
  -library 'Vale.Inline.X64.Fmul_inline' \
  -library 'Vale.Inline.X64.Fswap_inline' \
  -library 'Vale.Inline.X64.Fsqr_inline' \
  -no-prefix 'Vale.Inline.X64.Fadd_inline' \
  -no-prefix 'Vale.Inline.X64.Fmul_inline' \
  -no-prefix 'Vale.Inline.X64.Fswap_inline' \
  -no-prefix 'Vale.Inline.X64.Fsqr_inline' \
  -no-prefix 'EverCrypt.Vale'

FSTAR_FLAGS = \
  --cmi --query_stats \
  --z3rlimit_factor 16 \
  --cache_checked_modules \
  --odir $(OUTPUT_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS)) \
  --already_cached "*-Impl.EDHOC-Spec.EDHOC" \
  # --split_queries always \
  # --warn_error '+241@247+285-274' \

ENABLE_HINTS = \
  --use_hints --use_hint_hashes \
  --record_hints --hint_dir $(HINT_DIR)

FSTAR_COMMAND = $(FSTAR) $(FSTAR_FLAGS)

# === Targets ===
.PHONY: all verify clean distclean

all: verify

verify: $(CHECKED_FILES)

$(OUTPUT_DIR):
	mkdir -p $(OUTPUT_DIR)

$(HINT_DIR):
	mkdir -p $(HINT_DIR)

# %.fsti-in:
# 	@echo $(FSTAR_FLAGS) $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# %.checked: %.fst %.fsti | $(OUTPUT_DIR) $(HINT_DIR)
# 	@echo "Verifying $< ..."
# 	$(FSTAR_COMMAND) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $<).hints
# 	touch -c $@

$(OUTPUT_DIR)/%.checked: %.fst %.fsti | $(OUTPUT_DIR) $(HINT_DIR)
	@echo "Verifying $< ..."
	$(FSTAR_COMMAND) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints
	touch $@

clean:
	rm -rf $(OUTPUT_DIR) $(HINT_DIR) *.checked

distclean: clean
	rm -f .depend

