VFILES := BaseSS.v BaseBS.v BaseFix.v Pink.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	@if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) -f Makefile.coq Makefile.coq.conf

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq $(VFILES)

.PHONY: build clean

-include Makefile.coq
