all: compile

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

compile: Makefile.coq
	make -f Makefile.coq

install: Makefile.coq
	make -f Makefile.coq install

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
