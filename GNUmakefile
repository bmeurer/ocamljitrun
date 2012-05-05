#########################################################################
#                                                                       #
#                            Objective Caml                             #
#                                                                       #
#        Basile Starynkevitch, projet Cristal, INRIA Rocquencourt       #
#                                                                       #
#   Copyright 2004 Institut National de Recherche en Informatique et    #
#   en Automatique.  All rights reserved.  This file is distributed     #
#   under the terms of the GNU Library General Public License, with     #
#   the special exception on linking described in file ../LICENSE.      #
#                                                                       #
#########################################################################

# file ocamljitrun/GNUmakefile

# this is heavily inspired by (and depends upon) Ocaml top makefile
# (by Xavier Leroy et al.)

## this is a GNUmakefile since it uses GNU make features (vpath) 

# cvs $Id: GNUmakefile,v 1.22 2004-07-10 19:56:53 basile Exp $

# the _jitconfig.mk should define the following variables
# OCAML_TOPDIR absolute path to Ocaml top source directory
# LIGHTNING_INCLUDEDIR absolute path to GNU lightning includes


## include the generated configuration file
include _jitconfig.mk

## optionally include a handcrafted xtra stuff - see the EXTRA variables here
-include _jit_extra.mk

ifndef OCAMLJITVERSION
OCAMLJITVERSION=$(shell env LANG=C LC_TIME=C date +"snapshot_%Y_%b_%d_%Hh_%M")
endif
OCAML_BYTERUN= $(OCAML_TOPDIR)/byterun
SED=sed
RM=rm -vf
DATE=date
TAR=tar #gnu tar
TARDY=tardy
GAWK=awk
GZIP=gzip
JITDIR:=$(shell pwd)

ifndef OPTIMFLAGS
OPTIMFLAGS=-O2
endif

vpath %.c .:$(OCAML_BYTERUN)
vpath %.h .:$(OCAML_BYTERUN)
vpath primitives .:$(OCAML_BYTERUN)

vpath %.o 
vpath %.a
vpath %.obj
vpath %.lib

.PHONY: clean all debug distclean tests test1 test2 test3 test4 testinterp   tar

## on some local sites we could have debug in OCAML_JIT_EXTRA_ALL
all: ocamljitrun$(EXE) $(OCAML_JIT_EXTRA_ALL)

debug: ocamljitrund$(EXE)

_jitconfig.mk:
	@echo please run the ConfigureJit script or configure manually
	exit 1

# get the OBJS and PRIMS definitions from master byterun makefile
_ocamldef.mk: $(OCAML_BYTERUN)/Makefile
	$(DATE) +"# file $@ generated on %c ... " > $@
	echo "# ... from $^ " >> $@
	$(SED) -n  '/^OBJS=/,/[^\\]$$/p' < $^ >> $@
	$(SED) -n  '/^PRIMS=/,/[^\\]$$/p' < $^ >> $@
	$(GAWK) '/^[a-z]+.[hc] *:/{printf "%s:\n\t$$(MAKE) -C $$(OCAML_BYTERUN) $$@\n",$$1}' $^ >> $@

include $(OCAML_TOPDIR)/config/Makefile
include $(OCAML_BYTERUN)/.depend
include _ocamldef.mk

CC=$(BYTECC)
CFLAGS+=-DCAML_NAME_SPACE -DCAML_JIT -DLOCAL_CALLBACK_BYTECODE \
        -I$(OCAML_BYTERUN) -I$(LIGHTNING_INCLUDEDIR) $(BYTECCCOMPOPTS) $(OPTIMFLAGS)

JITOBJS:=$(patsubst interp.o,jitinterp.o,$(OBJS))
JITDEBUGOBJS:=$(patsubst %.o,%.d.o,$(JITOBJS))

TESTOCAMLJITRUN= ocamljitrun$(EXE)
install: ocamljitrun$(EXE) libcamljitrun.a
	cp ocamljitrun$(EXE) $(BINDIR)/ocamljitrun$(EXE)
	cp libcamljitrun.a $(LIBDIR)/libcamljitrun.a
	cd $(LIBDIR); $(RANLIB) libcamljitrun.a
#	cp ocamljitrund$(EXE) $(BINDIR)/ocamljitrund$(EXE)

ocamljitrun$(EXE): prims.o libcamljitrun.a 
	$(BYTECC)  $(BYTECCCOMPOPTS) $(BYTECCLINKOPTS) -o ocamljitrun$(EXE) \
	$^ $(BYTECCLIBS)

ocamljitrund$(EXE): $(OCAML_BYTERUN)/ocamlrund$(EXE) prims.d.o instrtrace.d.o libcamljitrund.a 
	$(BYTECC) -g $(BYTECCCOMPOPTS) $(BYTECCLINKOPTS) -o ocamljitrund$(EXE) \
	$(filter-out $<, $^) -ldisass $(BYTECCLIBS)

libcamljitrun.a: $(JITOBJS)
	ar rc $@ $^
	$(RANLIB) $@

libcamljitrund.a: $(JITDEBUGOBJS)
	ar rc $@ $^
	$(RANLIB) $@

$(OCAML_BYTERUN)/ocamlrund$(EXE):
	$(MAKE) -C $(OCAML_BYTERUN) ocamlrund$(EXE)
%.d.o: override OPTIMFLAGS+=-g  -DDEBUG
%.d.o: %.c
	$(BYTECC) $(CFLAGS) -Wall  -c $< -o $@

clean:
	$(RM) *.o *.a *.obj _t* core* *.so .*[0-9] testcallb \
          *.cmo *.cmi  ocamljitrun$(EXE) ocamljitrund$(EXE) *~ .*~ 
	$(MAKE) -C mlptrace clean

distclean: clean
	$(RM) _*

test_callback.so: test_callback.c
	$(CC) -O -g -shared -I $(OCAML_BYTERUN) -fPIC $^ -o $@

testcallb: testcallb.ml test_callback.so
	$(OCAML_TOPDIR)/ocamlc -nopervasives $^ -dllpath $(JITDIR) -dllib test_callback.so -o $@

tests: ocamljitrun$(EXE) ocamljitrund$(EXE) testinterp test1 test2 test3 test4
ifdef OCAMLJITBACKUPDIR
	cp jitinterp.c $(OCAMLJITBACKUPDIR)/$(shell date +"good_jitinterp.c_%d_%b_%Y_%T")
endif

test1:  $(TESTOCAMLJITRUN) ocamljitrun$(EXE) ocamljitrund$(EXE)
# dump for fun the ocamlc bytecode
	$(MAKE) -C $(OCAML_TOPDIR)/tools dumpobj
	$(JITDIR)/$(TESTOCAMLJITRUN) $(OCAML_TOPDIR)/tools/dumpobj $(OCAML_TOPDIR)/ocamlc > _test1.out
test2:  $(TESTOCAMLJITRUN) ocamljitrun$(EXE) ocamljitrund$(EXE)
# run the ocaml tests with the jitruntime
	cd $(OCAML_TOPDIR)/test; $(MAKE) bytetest CAMLRUN=$(JITDIR)/$(TESTOCAMLJITRUN)
test3: $(TESTOCAMLJITRUN) ocamljitrun$(EXE) ocamljitrund$(EXE)
# run ocamlc on scanf.ml
	cd $(OCAML_TOPDIR)/stdlib; $(JITDIR)/$(TESTOCAMLJITRUN) $(OCAML_TOPDIR)/ocamlc -warn-error A  -c scanf.ml
test4: $(TESTOCAMLJITRUN) testcallb ocamljitrun$(EXE) ocamljitrund$(EXE)
	$(JITDIR)/$(TESTOCAMLJITRUN) testcallb

testinterp: ocamljitrun$(EXE) ocamljitrund$(EXE)
	$(JITDIR)/testjit.sh

tar: clean
	$(TAR) -c -f - --exclude=CVS --exclude='_*' --exclude '*.o' --exclude '*.a' . \
        |  $(TARDY)  -Clean -Group_NAme src -Prefix ocamljit-$(OCAMLJITVERSION) | $(GZIP) -9 > ../ocamljit.tar.gz
#eof $Id: GNUmakefile,v 1.22 2004-07-10 19:56:53 basile Exp $
