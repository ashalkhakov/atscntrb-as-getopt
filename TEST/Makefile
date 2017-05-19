#
# A simple Makefile
#

######

PATSHOMEQ="$(PATSHOME)"

######

PATSCC=$(PATSHOMEQ)/bin/patscc
PATSOPT=$(PATSHOMEQ)/bin/patsopt

######

all::
regress::
cleanall::

######
#
all:: \
test00
test00: \
test00.dats ; \
$(PATSCC) \
-DATS_MEMALLOC_LIBC -o $@ $<
#
regress:: test00; ./$<
regress:: test00
	./test00 --help -W0 ab
	./test00 --help -- --another arg
	./test00 --output=A --help -Wl abc def
cleanall:: ; $(RMF) test00
#
######

RMF=rm -f

######

testall:: all
testall:: regress
testall:: cleanall

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o

######

cleanall:: clean

###### end of [Makefile] ######
