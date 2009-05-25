EMAKE = erl -make

default: tool

all: tool tests

tool:
	cd ebin; $(EMAKE)

clean:
	cd ebin; rm -f *.beam

tests:
	cd test; $(EMAKE)

tests_clean:
	cd ebin; rm -f ltl2buchi_eqc.beam ltl2buchi_wrap.beam wring_wrap.beam
