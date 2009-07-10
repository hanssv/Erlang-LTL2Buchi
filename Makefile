EMAKE = erl -make
ERL_LIB = /usr/lib/erlang/lib
VERSION = 1.0

default: tool

all: tool tests doc

src/ltl_parser.erl: src/ltl_parser.yrl
	cd src; erl -noshell -run yecc file ltl_parser -run erlang halt
	cd src; sed '1i%% @hidden' ltl_parser.erl > foo; mv foo ltl_parser.erl

tool: 	src/ltl_parser.erl
	cd ebin; $(EMAKE)

clean:
	cd ebin; rm -f *.beam ../src/ltl_parser.erl

tests:
	cd test; $(EMAKE)

tests_clean:
	cd ebin; rm -f ltl2buchi_eqc.beam ltl2buchi_wrap.beam wring_wrap.beam \
	modella_ltl2buchi.beam basic_ltl2buchi.beam simple_ltl2buchi.beam

doc: tool 
	echo "Building documentation in ./edoc"
	erl -noshell -eval "edoc:application('ltl2buchi',\".\",[{exclude_packages,[ltl_parser]}])" -s init stop 
	@cd doc; iconv -f LATIN1 -t UTF8 overview-summary.html > tmp; mv tmp overview-summary.html
	@cd doc; sed -e 's/Ã¼/ü/g' overview-summary.html > tmp; mv tmp overview-summary.html

install: tool tests_clean
	mkdir -p $(ERL_LIB)/ltl2buchi-$(VERSION)
	cp -r ebin doc src $(ERL_LIB)/ltl2buchi-$(VERSION)
