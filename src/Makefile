# === Directories ===
OUTPUT_DIR     = .output
HINT_DIR       = .hints
DEP_FILE       = .depend

include Makefile.include

ifeq (,$(FSTAR))
  $(error FSTAR is not defined)
endif

ifeq (,$(KRML_HOME))
  $(error KRML_HOME is not defined)
endif

ifeq (,$(HACL_HOME))
  $(error HACL_HOME is not defined)
endif

##########################
# Pretty-printing helper #
##########################


SHELL=/bin/bash
TIME=/usr/bin/time

to-obj-dir = $(addprefix obj/,$(notdir $1))

# A helper to generate pretty logs, callable as:
#   $(call run-with-log,CMD,TXT,STEM)
#
# Arguments:
#  CMD: command to execute (may contain double quotes, but not escaped)
#  TXT: readable text to print out once the command terminates
#  STEM: path stem for the logs, stdout will be in STEM.out, stderr in STEM.err, CMD in STEM.cmd
ifeq (,$(NOSHORTLOG))
run-with-log = \
  @echo "$(subst ",\",$1)" > $3.cmd; \
  $(TIME) -q -f '%E' -o $3.time sh -c "$(subst ",\",$1)" > $3.out 2> >( tee $3.err 1>&2 ); \
  ret=$$?; \
  time=$$(cat $3.time); \
  if [ $$ret -eq 0 ]; then \
    echo "$2, $$time"; \
  else \
    echo "<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>"; \
    echo -e "\033[31mFatal error while running\033[0m: $1"; \
    echo -e "\033[31mFailed after\033[0m: $$time"; \
    echo -e "\033[36mFull log is in $3.{out,err}, see excerpt below\033[0m:"; \
    tail -n 20 $3.err; \
    echo "<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>"; \
    false; \
  fi
else
run-with-log = $1
endif


# === File Discovery ===
FSTAR_FILES    = $(wildcard *.fst)
CHECKED_FILES  = $(addprefix $(OUTPUT_DIR)/, $(FSTAR_FILES:.fst=.checked))

# Main entry points (first one is default)

# all: verify
all: dist/libkemedhoc.a


.PHONY: clean
clean:
	rm -f -r ./obj/* ./dist/*


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

# === Definitions of FStar flags ===

ENABLE_HINTS = \
  --use_hints --use_hint_hashes \
  --record_hints

# Some reasonable flags to turn on:
# - 247: checked file not written because some of its dependencies...
# - 285: missing or file not found, almost always something to act on
# - 241: stale dependencies, almost always a sign that the build is incorrect
#
# But also:
# - --cmi, for cross-module inlining, a must-have for anyone who relies on
#   inline_for_extraction in the presence of interfaces
# - --cache_dir, to place checked files there
FSTAR_FLAGS = \
  --cmi --query_stats \
  --z3rlimit_factor 16 \
  --cache_checked_modules $(FSTAR_INCLUDES) \
  --odir obj \
  --already_cached "* -Impl.EDHOC -Spec.EDHOC" --warn_error '+241@247+285' \
  --cache_dir obj --hint_dir hints \

# Important to wildcard both fst and fsti since there are fstis without fsts.
FSTAR_ROOTS = $(EDHOC_HOME)/*.fsti \
  $(addsuffix /*.fst,$(SOURCE_DIRS)) \

FSTAR_COMMAND = $(FSTAR) $(FSTAR_FLAGS)

FSTAR_EXTRACT =

# This is the only bulletproof way that I know of forcing a regeneration of the
# .depend file every single time. Why, you may ask? Well, it's frequent enough
# to add a new file that you don't want to decipher a cryptic error only to
# remember you should run `make depend`. Also, if you move files around, it's
# good to force regeneration even though .depend may be more recent than the
# mtime of the moved files.
ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(call run-with-log,\
	  $(FSTAR_COMMAND) --dep full $(FSTAR_ROOTS) > $@\
	  ,[FSTAR-DEPEND],$(call to-obj-dir,depend))

.PHONY: .FORCE
.FORCE:
endif
endif

# ifeq (,$(filter %-in,$(MAKECMDGOALS)))
# include .depend
# endif
include .depend


# Verification
# ------------

# Creating these directories via a make rule, rather than rely on F* creating
# them, as two calls to F* might race.
hints:
	mkdir $@

obj:
	mkdir $@

# We allow some specific pattern rules to be added here, relying on the shortest
# stem rule for them to take precedence. For instance, you may want to do:
#
# obj/Bignum.Impl.fst.checked: FSTAR_FLAGS = "--query_stats"
#
# (Note: for options that control the SMT encoding, such as
# --smtencoding.nl_arith_repr native, please make sure you also define them in
# Makefile.common for %.fst-in otherwise you'll observe different behaviors
# between interactive and batch modes.)
#
# By default, however, variables are inherited through the dependencies, meaning
# that the example above would normally set these FSTAR_FLAGS for any .checked
# that is rebuilt because it's a dependency of Bignum.Impl.fst.checked.
#
# To avoid this unpleasant behavior, the most general pattern rule (longest
# stem) also defines a suitable default value for FSTAR_FLAGS.
%.checked: FSTAR_FLAGS=


# Note: F* will not change the mtime of a checked file if it is
# up-to-date (checksum matches, file unchanged), but this will confuse
# make and result in endless rebuilds. So, we touch that file.
%.checked: | hints obj
	$(call run-with-log, \
	  $(FSTAR) $< $(FSTAR_FLAGS) && touch -c $@ \
	  ,[VERIFY] $(notdir $*),$(call to-obj-dir,$@))

# Extraction
# ----------

.PRECIOUS: obj/%.krml
obj/%.krml:
	$(call run-with-log, \
	  $(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<)))\
	  ,[EXTRACT-KRML] $(notdir $*),$(call to-obj-dir,$@))

# F* --> C
# --------

KRML=krml

# Note: the implementation of the intrinsic uses external linkage, but you could
# easily turn this file into a .h, use -add-include '"Impl_Bignum_Intrinsics.h"'
# and pass -static-header Impl.Bignum.Intrinsics as described in the
# documentation.
HAND_WRITTEN_C_FILES =

# This is now the preferred and recommended way to compile C code with KaRaMeL.
#
# KaRaMeL (via -skip-compilation) only generates a stub Makefile in dist/,
# instead of acting as a C compilation driver like it did before. The Makefile
# that is generated by KaRaMeL is basic, but takes into account:
# - the -o option to determine what is being built
# - the C files passed on the command line, which will be linked together
# - C compiler flags passed to KaRaMeL via -ccopts
#
# This Makefile is called Makefile.basic and should be enough for all your basic
# needs. If you need something more fancy, you can easily author your own custom
# dist/Makefile, which includes Makefile.basic, then proceeds to redefine /
# tweak some variables.
#
# Note that you are of course more than welcome to define your own
# CMakeLists.txt or whatever your favorite build system is: this tutorial only
# describes the supported canonical way of compiling code.
#
# See the advanced topics section for an in-depth explanation of how the -bundle
# option works. We also use -minimal.
EDHOC_CORE_BUNDLE = -bundle 'Impl.EDHOC.Core=Impl.EDHOC.Core.*'

KRML_FLAGS += -header c/header.h

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES)) $(HAND_WRITTEN_C_FILES)
	mkdir -p $(dir $@)
	$(KRML) -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -warn-error @4@5@18 \
	  -fparentheses \
	  -fnoanonymous-unions \
          $(VALE_BUNDLES) \
          $(ADDITIONAL_VALE_KRML_FLAGS) \
          -bundle 'EverCrypt,EverCrypt.\*[rename=EverCrypt]' \
          -library EverCrypt,EverCrypt.* \
          -bundle 'FStar.\*,LowStar.\*,C,C.\*[rename=Mitls_Kremlib]' \
    $(EDHOC_CORE_BUNDLE) \
	  -bundle '*[rename=Hacl]'\
	  -library Hacl.* \
	  -minimal \
	  -add-include '<stdint.h>' \
	  -add-include '"krml/internal/target.h"' \
    -add-include '"krml/internal/types.h"' \
	  $(notdir $(HAND_WRITTEN_C_FILES)) \
	  -o libkemedhoc.a \
    $(KRML_FLAGS)

# Compiling the generated C code
# ------------------------------

# Here we do a recursive make invocation because a new dependency analysis needs
# to be performed on the generated C files. This recursive make deals with all
# the files copied in dist, which includes karamel-generated and hand-written,
# copied files from HAND_WRITTEN_C_FILES.

dist/libkemedhoc.a: dist/Makefile.basic
	$(MAKE) -C $(dir $@) -f $(notdir $<)
