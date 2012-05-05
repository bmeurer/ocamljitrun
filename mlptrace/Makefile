# file mlptrace/Makefile
# cvsid $Id: Makefile,v 1.7 2004-04-24 21:38:54 basile Exp $

RM=rm -vf
include ../_jitconfig.mk

OCAMLOPT=$(OCAML_TOPDIR)/ocamlopt.opt 
OCAMLFLAGS=-I $(OCAML_TOPDIR)/stdlib -I $(OCAML_TOPDIR)/otherlibs/unix -dtypes # -I $(OCAML_TOPDIR)/otherlibs/systhreads -thread
CC=gcc
CFLAGS=-g  -DNO_BLOCKING_SECTION
RM=rm -vf
.PHONY: all clean

all: $(OCAMLOPT) dbgjit 
	sync

clean:
	$(RM) *~ core *.o *.cm* *.annot dbgjit.prev dbgjit .*[0-9]

dbgjit: dbgutil.cmx dbgjit.cmx mlptrace.o
	if [ -f $@ ]; then mv $@ $@.prev; fi
	$(OCAMLOPT) $(OCAMLFLAGS) unix.cmxa dbgutil.cmx dbgjit.cmx mlptrace.o -o dbgjit

%.cmx: %.ml 
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<
%.cmi: %.mli
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

dbgjit.cmx dbgutil.cmx: dbgutil.cmi

%.o: %.c
	$(OCAMLOPT) $(OCAMLFLAGS) -ccopt "$(CFLAGS)" -c $^

$(OCAMLOPT):
	cd $(OCAML_TOPDIR); $(MAKE) opt.opt

ocamljitrund: 
	cd ..; $(MAKE) ocamljitrund
# eof $Id: Makefile,v 1.7 2004-04-24 21:38:54 basile Exp $