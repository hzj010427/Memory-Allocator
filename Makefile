#
# Student makefile for Malloc Lab
#
SHELL = /bin/bash
DOC = doxygen
CC = $(LLVM_PATH)clang
CXX = $(LLVM_PATH)clang++
CLANG_FORMAT = clang-format
LLVM_OPT = opt

# Flags used to compile mdriver-dbg
# You can edit these freely to change how your debug binary compiles.
COPT_DBG = -O0
CFLAGS_DBG = -DDEBUG=1

# Flags used to compile normally
COPT = -O0
CFLAGS = -std=c11 $(COPT) -g -Werror -Wall -Wextra -Wpedantic -Wconversion
CFLAGS += -Wstrict-prototypes -Wmissing-prototypes -Wwrite-strings
CFLAGS += -Wno-unused-function -Wno-unused-parameter -Wno-zero-length-array

# Macro checker configuration
MC = ./macro-check.pl
MCHECK = $(MC) -i dbg_

###########################################################
# Driver programs
###########################################################

DRIVERS = mdriver mdriver-dbg mdriver-emulate #mdriver-uninit
all: $(DRIVERS)
.PHONY: all

# Alternate main-build rule that skips everything built with custom
# instrumentation.  For testing with compilers that don't support
# the specific plugin API expected by our plugins.
all-but-instrumented: $(filter-out mdriver-emulate mdriver-uninit,$(DRIVERS))
.PHONY: all-but-instrumented

$(DRIVERS):
	$(CC) $(LDFLAGS) -o $@ $^ $(LDLIBS)

# Object files
mdriver:         mdriver.o        mm-native.o     memlib.o      tracefile.o
mdriver-dbg:     mdriver-dbg.o    mm-native-dbg.o memlib-asan.o tracefile-asan.o
mdriver-emulate: mdriver-sparse.o mm-emulate.o    memlib.o      tracefile.o
mdriver-uninit:  mdriver-msan.o   mm-msan.o       memlib-msan.o tracefile-msan.o
$(DRIVERS): fcyc.o clock.o stree.o

# Per-object-file flags
memlib.o memlib-asan.o memlib-msan.o: CFLAGS += -DNO_CHECK_UB

mdriver-sparse.o:                       CFLAGS += -DDRIVER -DSPARSE_MODE
mdriver.o mdriver-dbg.o mdriver-msan.o: CFLAGS += -DDRIVER
mm-emulate.ll mm-msan.ll:               CFLAGS += -DDRIVER
mm-native.o mm-native-dbg.o:            CFLAGS += -DDRIVER

mm-msan.o:    COPT  = -Og -fno-inline -fno-optimize-sibling-calls
mm-msan.o:    COPT += -fno-omit-frame-pointer
mm-emulate.o: COPT += -fno-vectorize

%-dbg.o: COPT = $(COPT_DBG)
%-dbg.o: CFLAGS += $(CFLAGS_DBG)

# Per-program and per-object-file flags (ASan, MSan)
mm-native-dbg.o memlib-asan.o tracefile-asan.o: \
  CFLAGS += -fsanitize=address,undefined -DUSE_ASAN
mdriver-dbg: LDFLAGS += -fsanitize=address,undefined

mm-msan.o mdriver-msan.o memlib-msan.o tracefile-msan.o: \
  CFLAGS += -fsanitize=memory -fsanitize-memory-track-origins -DUSE_MSAN
mdriver-uninit: \
  LDFLAGS += -fsanitize=memory -fsanitize-memory-track-origins

# Object files that don't match the builtin %.o:%.c rule
mm-native.o mm-native-dbg.o: mm.c
	$(COMPILE.c) -o $@ $<

mdriver-sparse.o mdriver-msan.o mdriver-dbg.o: mdriver.c
	$(COMPILE.c) -o $@ $<

memlib-asan.o memlib-msan.o: memlib.c
	$(COMPILE.c) -o $@ $<

tracefile-asan.o tracefile-msan.o: tracefile.c
	$(COMPILE.c) -o $@ $<

# Object files built with custom instrumentation
%.o: %.bc
	$(CC) $(COPT) -c -o $@ $<

mm-emulate.bc: mm-emulate.ll inst/MLabInst.so
	$(LLVM_OPT) -enable-new-pm=0 -load=inst/MLabInst.so -MLabInst -o $@ $<

#mm-msan.bc: mm-msan.ll inst/MLabInst2.so
#	$(LLVM_OPT) -enable-new-pm=0 -load=inst/MLabInst2.so -MLabInst -o $@ $<

mm-emulate.ll mm-msan.ll: mm.c
	$(CC) $(CFLAGS) -emit-llvm -S -o $@ $<

# Header file dependencies
clock.o: clock.c clock.h
decl.o: decl.c
fcyc.o: fcyc.c clock.h fcyc.h
stree.o: stree.c stree.h
stree_test.o: stree_test.c stree.h

mdriver.o mdriver-spars.o mdriver-msan.o mdriver-dbg.o: \
  mdriver.c config.h fcyc.h memlib.h mm.h stree.h tracefile.h
memlib.o memlib-asan.o memlib-msan.o: memlib.c config.h memlib.h
tracefile.o tracefile-asan.o tracefile-msan.o: tracefile.h

mm-native.o: mm.c memlib.h mm.h
mm-native-dbg.o: mm.c memlib.h mm.h
mm-emulate.ll: mm.c memlib.h mm.h
mm-msan.ll: mm.c memlib.h mm.h

###########################################################
# Macro check script
###########################################################

.PHONY: mm-check
mm-check: .macros-checked

.macros-checked: mm.c $(MC)
	$(MCHECK) -f $<
	touch $@

###########################################################
# Other rules
###########################################################

.PHONY: clean
clean:
	rm -f *.o *.bc *.ll
	rm -f $(DRIVERS) .format-checked .macros-checked

.PHONY: doc
doc: doxygen.conf mm.c mm.h memlib.h
	$(DOC) $<

# Include rules for submit, format, etc
FORMAT_FILES = mm.c
HANDIN_FILES = mm.c .clang-format .format-checked .macros-checked
HANDIN_TAR   = malloclab-handin.tar
HANDOUT_SCRIPTS =      \
    calibrate.pl       \
    check-format       \
    driver.pl          \
    macro-check.pl     \
    mdriver-cp-ref     \
    mdriver-ref        \
    inst/MLabInst.so

include helper.mk