EMAKE = erl -make

default: tool

all: tool tests doc

tool:
	cd src; erl -noshell -eval "yecc:yecc(\"ltl_parser.yrl\", \"ltl_parser.erl\")" -s init stop
	cd src; sed '1i%% @hidden' ltl_parser.erl > foo; mv foo ltl_parser.erl
	cd ebin; $(EMAKE)

clean:
	cd ebin; rm -f *.beam

tests:
	cd test; $(EMAKE)

tests_clean:
	cd ebin; rm -f ltl2buchi_eqc.beam ltl2buchi_wrap.beam wring_wrap.beam

doc: tool 
	echo "Building documentation in ./edoc"
	erl -noshell -eval "edoc:application('ltl2buchi',\".\",[{exclude_packages,[ltl_parser]}])" -s init stop 
	iconv -f LATIN1 -t UTF-8 doc/overview-summary.html > tmp; mv tmp doc/overview-summary.html
