EMAKE = erl -make

default: tool

all: tool tests doc

tool:
	cd src; erl -noshell -eval "yecc:yecc(\"ltl_parser.yrl\", \"ltl_parser.erl\")" -s init stop
	cd ebin; $(EMAKE)

clean:
	cd ebin; rm -f *.beam

tests:
	cd test; $(EMAKE)

tests_clean:
	cd ebin; rm -f ltl2buchi_eqc.beam ltl2buchi_wrap.beam wring_wrap.beam

doc: tool 
	echo "Building documentation in ./edoc"
	erl -noshell -eval "edoc:application('ltl2buchi',\".\",[])" -s init stop 
