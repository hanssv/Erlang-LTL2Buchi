Rootsymbol formula.
Nonterminals form prop formula.
Terminals atom '(' ')' '=' integer until always next eventually or and not release equivalent implies false true var.
Right 40 implies.
Right 30 equivalent.
Left  50 or and.
Right 60 until release.
Right 70 eventually always.
Nonassoc 80 next.
Nonassoc 90 not.
Nonassoc 100 atom. 
formula -> form : '$1'.
form -> '(' form ')' : '$2'.
form -> true : ltl:ltrue().
form -> false : ltl:lfalse().
form -> prop : '$1'.
form -> not form : ltl:lnot('$2').
form -> next form : ltl:next('$2').
form -> always form : ltl:always('$2').
form -> eventually form : ltl:eventually('$2').
form -> form until form : ltl:until('$1','$3').
form -> form release form : ltl:release('$1','$3').
form -> form or form : ltl:lor('$1','$3').
form -> form and form : ltl:land('$1','$3').
form -> form implies form : ltl:implication('$1','$3').
form -> form equivalent form : ltl:equivalent('$1','$3').
prop -> atom '=' integer :  
  case element(3,'$3') of
    1 ->
      ltl:prop(element(3,'$1'));
	_ ->
	  ltl:lnot(ltl:prop(element(3,'$1')))
  end.
prop -> atom : 
  ltl:prop(element(3,'$1')).
prop -> var :  
  ltl:prop({'var',element(3,'$1')}).

		   

			 


