all: Makefile.coq compile install

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

compile:
	make -f Makefile.coq all

install:
	make -f Makefile.coq install

clean:
	make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
