all: Makefile.coq all install

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

all:
	make -f Makefile.coq all

install:
	make -f Makefile.coq install
