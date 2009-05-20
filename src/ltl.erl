%% Copyright (c) 2009, Hans Svensson
%% All rights reserved.
%%
%% Redistribution and use in source and binary forms, with or without
%% modification, are permitted provided that the following conditions are met:
%%     %% Redistributions of source code must retain the above copyright
%%       notice, this list of conditions and the following disclaimer.
%%     %% Redistributions in binary form must reproduce the above copyright
%%       notice, this list of conditions and the following disclaimer in the
%%       documentation and/or other materials provided with the distribution.
%%     %% Neither the name of the copyright holders nor the
%%       names of its contributors may be used to endorse or promote products
%%       derived from this software without specific prior written permission.
%%
%% THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ''AS IS''
%% AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
%% IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
%% ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS AND CONTRIBUTORS 
%% BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
%% CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF 
%% SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR 
%% BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
%% WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR 
%% OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF 
%% ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

-module(ltl).

-compile(export_all).

prop(X) ->
    {lprop, X}.

next(Phi) ->
	{next,Phi}.

always(Phi) ->
	{always,Phi}.

eventually(Phi) ->
	{eventually,Phi}.

until(Psi,Phi) ->
	{until,Psi,Phi}.

release(Psi,Phi) ->
	{release,Psi,Phi}.

lnot(Phi) ->
    {lnot, Phi}.

land(Phi1, Phi2) ->
    {land, Phi1, Phi2}.

land([]) -> ltl_true;
land([Phi]) -> Phi;
land([Phi| Phis]) -> {land, Phi, land(Phis)}.

lor(Phi1, Phi2) ->
    {lor, Phi1, Phi2}.

lor([]) -> lfalse;
lor([Phi]) -> Phi;
lor([Phi| Phis]) -> {lor, Phi, lor(Phis)}.

implication(Phi1, Phi2) ->
    {lor, {lnot, Phi1}, Phi2}.

equivalent(Phi1, Phi2) ->
    land(implication(Phi1, Phi2), implication(Phi2, Phi1)).

ltrue() -> 
	ltrue.

lfalse() -> 
	lfalse.

%% Negate an ltl_formula
negate(lfalse) -> ltrue;
negate(ltrue) -> lfalse;
negate({lnot, X}) -> X;
negate(Phi) -> lnot(Phi).

%% Normalize (sort ands and ors)
normalize({land, Phi1, Phi2}) ->
    land(lists:usort([normalize(Phi1), normalize(Phi2)]));
normalize({lor, Phi1, Phi2}) ->
    lor(lists:usort([normalize(Phi1), normalize(Phi2)]));
normalize({Op, Phi}) -> {Op, normalize(Phi)};
normalize({Op, Phi1, Phi2}) -> {Op, normalize(Phi1), normalize(Phi2)};
normalize(Phi) -> Phi.
	

%% The subformulas of an ltl_formula
subformulas(X = {lprop,_}) ->              [X];
subformulas(Phi0 = {_Op,Phi}) ->         [Phi0 | subformulas(Phi)];
subformulas(Phi0 = {_Op,Phi1,Phi2}) ->   [Phi0 | subformulas(Phi1) ++ subformulas(Phi2)];
subformulas(Phi) ->                      [Phi].

%% Positive normal form (i.e. pushing the negations inwards)
pnf({lnot,{always,Phi}}) ->         {eventually,pnf({lnot,Phi})};
pnf({lnot,{eventually,Phi}}) ->     {always,pnf({lnot,Phi})};
pnf({lnot,{next,Phi}}) ->           {next,pnf({lnot,Phi})};
pnf({lnot,{until,Psi,Phi}}) ->      {release,pnf({lnot,Psi}),pnf({lnot,Phi})};
pnf({lnot,{release,Psi,Phi}}) ->    {until,pnf({lnot,Psi}),pnf({lnot,Phi})};
pnf({lnot,{lnot,Phi}}) ->           pnf(Phi);
pnf({lnot,{land,Phi1,Phi2}}) ->     {lor,pnf({lnot,Phi1}),pnf({lnot,Phi2})};
pnf({lnot,{lor,Phi1,Phi2}}) ->      {land,pnf({lnot,Phi1}),pnf({lnot,Phi2})};
pnf({lnot,{ltrue}}) ->              lfalse;
pnf({lnot,{lfalse}}) ->             ltrue;
pnf({Op,Phi}) ->                    {Op,pnf(Phi)};
pnf({Op,Phi1,Phi2}) ->              {Op,pnf(Phi1),pnf(Phi2)};
pnf(Phi) ->                         Phi.

%% Rewrite rules (heuristics?) from the Wring paper
ltl_rewrite({until,{next,Phi1},{next,Phi2}}) -> 
	ltl_rewrite({next,{until,Phi1,Phi2}});
ltl_rewrite({land,{release,Psi,Phi1},{release,Psi,Phi2}}) ->
	ltl_rewrite({release,Psi,{land,Phi1,Phi2}});
ltl_rewrite({lor,{release,Psi1,Phi},{release,Psi2,Phi}}) ->
	ltl_rewrite({release,{lor,Psi1,Psi2},Phi});
ltl_rewrite({lor,{until,Psi,Phi1},{until,Psi,Phi2}}) ->
	ltl_rewrite({release,Psi,{land,Phi1,Phi2}});
ltl_rewrite({land,{release,Psi1,Phi},{release,Psi2,Phi}}) ->
	ltl_rewrite({release,{land,Psi1,Psi2},Phi});
ltl_rewrite({land,{next,Phi1},{next,Phi2}}) ->
	ltl_rewrite({next,{land,Phi1,Phi2}});
ltl_rewrite({lor,{next,Phi1},{next,Phi2}}) ->
	ltl_rewrite({next,{lor,Phi1,Phi2}});
ltl_rewrite({next,ltrue}) ->
	ltrue;
ltl_rewrite({until,_,lfalse}) ->
	lfalse;
ltl_rewrite({lor,{always,{eventually,Phi1}},{always,{eventually,Phi2}}}) ->
	ltl_rewrite({always,{eventually,{lor,Phi1,Phi2}}});
ltl_rewrite({eventually,{next,Phi}}) ->
 	ltl_rewrite({next,{eventually,Phi}});
ltl_rewrite({eventually,{always,{eventually,Phi}}}) ->
 	ltl_rewrite({always,{eventually,Phi}});
ltl_rewrite({until,_Psi,{always,{eventually,Phi}}}) ->
	ltl_rewrite({always,{eventually,Phi}});
ltl_rewrite({release,_Psi,{always,{eventually,Phi}}}) ->
	ltl_rewrite({always,{eventually,Phi}});
ltl_rewrite({next,{always,{eventually,Phi}}}) ->
	ltl_rewrite({always,{eventually,Phi}});
ltl_rewrite({eventually,{land,Phi1,{always,{eventually,Phi2}}}}) ->
	ltl_rewrite({land,{eventually,Phi1},{always,{eventually,Phi2}}});
ltl_rewrite({always,{lor,Phi1,{always,{eventually,Phi2}}}}) ->
	ltl_rewrite({lor,{always,Phi1},{always,{eventually,Phi2}}});
ltl_rewrite({next,{land,Phi1,{always,{eventually,Phi2}}}}) ->
	ltl_rewrite({land,{next,Phi1},{always,{eventually,Phi2}}});
ltl_rewrite({next,{lor,Phi1,{always,{eventually,Phi2}}}}) ->
	ltl_rewrite({lor,{next,Phi1},{always,{eventually,Phi2}}});
ltl_rewrite({Op,Phi}) -> 
	{Op,ltl_rewrite(Phi)};
ltl_rewrite({Op,Phi1,Phi2}) ->
	{Op,ltl_rewrite(Phi1),ltl_rewrite(Phi2)};
ltl_rewrite(Phi) -> 
	Phi.


rew_rules() ->
		[{{land,phi,phi},           phi},
		 {{land,phi,lfalse},     lfalse},
		 {{land,lfalse,phi},     lfalse},
		 {{land,phi,ltrue},      phi},
		 {{land,ltrue,phi},      phi},
		 {{land,phi,{lnot,phi}}, lfalse},
		 {{land,{lnot,phi},phi}, lfalse},
		 %% OR
		 {{lor,phi,phi},            phi},
		 {{lor,phi,lfalse},      phi},
		 {{lor,lfalse,phi},      phi},
		 {{lor,phi,ltrue},       ltrue},
		 {{lor,ltrue,phi},       ltrue},
		 {{lor,phi,{lnot,phi}},  ltrue},
		 {{lor,{lnot,phi},phi},  ltrue}].
		 
use_rule({To,From}, Phi) ->
		ok.
		 						
rewrite({land,P1,P2}) ->
		ok.
	
	

%% Print a set of ltl formulas, not beautiful ;-)
print_sets_ltl(Xs) when is_list(Xs) ->
	lists:map(fun print_sets_ltl/1,Xs);
print_sets_ltl(X) ->
	print_ltl(X).

print_covers(Xs) ->	
	lists:map(fun print_cover1/1,Xs).

print_cover1({Phi, Xs}) ->
    [print_ltl(Phi) ++ " => "| lists:map(fun print_cover2/1, Xs)].
print_cover2({Vars,Nexts}) ->
	 lists:map(fun print_ltl/1,Vars) ++ lists:map(fun print_ltl/1,Nexts).


%% Generic printing of LTL expressions
pp(F) ->
	pp(F,normal).

pp({lprop,X},S) ->
	pp_lprop(atom_to_list(X),S);
pp({lor,Phi1,Phi2},S) ->
	case op_prio(Phi1,S) >= op_prio(lor,S) of
		true  -> "(" ++ pp(Phi1,S) ++ ")" ++ ltl_sym(lor,S);
		false -> pp(Phi1,S) ++ ltl_sym(lor,S)
	end 
		++
	case op_prio(Phi2,S) >= op_prio(lor,S) of
		true  -> "(" ++ pp(Phi2,S) ++ ")";
		false -> pp(Phi2,S)
	end; 
pp({land,Phi1,Phi2},S) ->
	case op_prio(Phi1,S) >= op_prio(land,S) of
		true  -> "(" ++ pp(Phi1,S) ++ ")" ++ ltl_sym(land,S);
		false -> pp(Phi1,S) ++ ltl_sym(land,S)
	end 
		++
	case op_prio(Phi2,S) >= op_prio(land,S) of
		true  -> "(" ++ pp(Phi2,S) ++ ")";
		false -> pp(Phi2,S)
	end; 
pp({until,Psi,Phi},S) ->
	case op_prio(Psi,S) >= op_prio(until,S) of
		true  -> "(" ++ pp(Psi,S) ++ ")" ++ ltl_sym(until,S);
		false -> pp(Psi,S) ++ ltl_sym(until,S)
    end 
		++
	case op_prio(Phi,S) >= op_prio(until,S) of
		true  -> "(" ++ pp(Phi,S) ++ ")";
		false -> pp(Phi,S)
    end;
pp({release,Psi,Phi},S) ->
	case op_prio(Psi,S) >= op_prio(release,S) of
		true  -> "(" ++ pp(Psi,S) ++ ")" ++ ltl_sym(release,S);
		false -> pp(Psi,S) ++ ltl_sym(release,S)
    end 
		++
	case op_prio(Phi,S) >= op_prio(release,S) of
		true  -> "(" ++ pp(Phi,S) ++ ")";
		false -> pp(Phi,S)
    end;
pp({Op,Phi},S) -> %% [],<>,!,X
	case op_prio(Phi,S) >= op_prio(Op,S) of
		true  -> ltl_sym(Op,S) ++ "(" ++ pp(Phi,S) ++ ")";
		false -> ltl_sym(Op,S) ++ pp(Phi,S)
	end;
pp(X,_S) when is_atom(X) ->
	atom_to_list(X).

pp_lprop(X,wring) ->
	X ++ "=1";
pp_lprop(X,_) ->
	X.

op_prio(X,wring) ->
	op_prio_wring(X);
op_prio(X,_) ->
	op_prio(X).

op_prio(X) when is_tuple(X) ->
	op_prio(element(1,X));
op_prio(lor)     -> 10;
op_prio(land)    -> 10; 
op_prio(until)      -> 6;
op_prio(release)    -> 6;
op_prio(eventually) -> 5;
op_prio(always)     -> 5;
op_prio(next)       -> 4;
op_prio(lnot)    -> 3;
op_prio(lprop)        -> 1;
op_prio(_) -> 1.

op_prio_wring(_) -> 1.

ltl_sym(X,normal) -> normal_sym(X);
ltl_sym(X,java)   -> java_sym(X);
ltl_sym(X,wring)  -> wring_sym(X).

normal_sym(lor)      -> " | ";
normal_sym(land)     -> " & ";
normal_sym(until)       -> " U ";
normal_sym(release)     -> " R ";
normal_sym(eventually)  -> "F ";
normal_sym(always)      -> "G ";
normal_sym(next)        -> "X ";
normal_sym(lnot)     -> "!".

wring_sym(lor)      -> "+";
wring_sym(land)     -> "*";
wring_sym(until)       -> "U";
wring_sym(release)     -> "R";
wring_sym(eventually)  -> "F";
wring_sym(always)      -> "G";
wring_sym(next)        -> "X";
wring_sym(lnot)     -> "!".

java_sym(lor)      -> " || ";
java_sym(land)     -> " && ";
java_sym(until)       -> " U ";
java_sym(release)     -> " V ";
java_sym(eventually)  -> "<> ";
java_sym(always)      -> "[] ";
java_sym(next)        -> "X ";
java_sym(lnot)     -> "!".

print_ltl(Phi) -> pp(Phi,normal).

%%%%%%%%%%%
%% Some simple tests
%%%%%%%%%%%
ltl1() ->
	{lor,{until,{next,{lprop,p}},{next,{lprop,q}}},{lnot,{next,{until,{lprop,p},{lprop,q}}}}}.

ltl2() ->
    {land, {eventually, prop(p)}, {eventually, lnot(prop(p))}}.

ltl3() -> {land, prop(a), {lor, prop(b), prop(c)}}.

ltl4() ->
    {land, {land, prop(a), prop(b)}, {land, prop(c), {lor, prop(d), prop(e)}}}.

ltl5() ->
    {lor, {next, prop(p)}, {land, prop(p), {next, {always, prop(p)}}}}.

ltl6() -> {eventually, {always, prop(p)}}.

ltl6b() -> {always, {eventually, prop(p)}}.

ltl7() -> {eventually, {always, {lor, prop(p), prop(q)}}}.

ltl8() ->
    {land, {lor, prop(p), {next, phi1}}, {lor, prop(q), {next, phi2}}}.

ltl9() ->
    {land, {lor, prop(a), prop(b)}, {lor, prop(c), prop(d)}}.

ltl10() ->
    {land, {eventually, {always, prop(p)}}, {eventually, {always, prop(q)}}}.

ltl11() ->
	{always,{land,{eventually,{lprop,p}},{eventually,{lprop,q}}}}.

ltl12() -> {until, prop(p), prop(q)}.

ltl13() -> {always, prop(p)}.

ltl14() -> {eventually, {land, {lnot, prop(p)}, prop(p)}}.

ltl15() ->
    {eventually, {next, {land, {lnot, prop(p)}, prop(p)}}}.

ltl16() ->
    implication({eventually, {always, prop(p0)}}, {eventually, prop(p0)}).

bas1() -> {until, prop(p1), prop(p2)}.

bas2() -> {until, prop(p1), {until, prop(p2), prop(p3)}}.
