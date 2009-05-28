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

-module(ltl2buchi_eqc).

-compile(export_all).

-include_lib("eqc/include/eqc.hrl").

%%
%% Data types / records
%%

%% witness a k a trace
%% Note: this is a (simplified) Kripke structure, and thus all
%%       prop. vars. have an explicit value.
-record(witness,{alpha = [], prefix = [], loop = []}).

%%
%% Generators
%%
w_timeout(Fun, Arg) ->
    ?LET(X, (elements([Arg])), (Fun(X))).

lprop() ->
    elements([{lprop,X} || X <- [a,b,c,d,e,h]]).

%% A setification of non-empty list (list1)
alpha() -> ?LET(Lst, (list1(lprop())), (lists:usort(Lst))).

%% A set of literals (pos and neg)
literals(Alpha) ->
    ?LET({Signs, Set}, {list(bool()), set(Alpha)},
         (sign(Signs, Set))).

sign(_,[]) -> [];
sign([],S) -> S;
sign([true|Signs],[V|Set]) -> [{lnot,V}|sign(Signs,Set)];
sign([_|Signs],[V|Set]) -> [V | sign(Signs,Set)].

%% A label (given an alphabet)
label(Alpha) ->
    ?LET(Signs, (vector(length(Alpha), bool())), (sign(Signs, Alpha))).

%% Non-empty list
list1(G) -> [G | list(G)].

set(Lst) ->
    ?LET(SLst, (list(elements(Lst))), (lists:usort(SLst))).

set_ne(Lst) ->
    ?LET(SLst, (list1(elements(Lst))), (lists:usort(SLst))).

%% Generate a witness
witness() -> ?LET(Alpha, (alpha()), (witness(Alpha))).

witness(Alpha) ->
    #witness{alpha  = Alpha,
             prefix = list(label(Alpha)),
             loop   = list1(label(Alpha))}.

witness_for_buchi(B) ->
    ?LET(Alpha, (alpha()), (witness_for_buchi(Alpha, B))).

witness_for_buchi(A, B = {_States, InitStates, Trans, Accept}) ->
	{ok,G} = buchi:buchi2digraph(B),
	Reachable = digraph_utils:reachable(InitStates,G),
	Choices = [ {digraph:get_cycle(G,V),digraph:get_path(G,1,V)} || 
				  V <- Accept,
				  lists:member(V,Reachable),
				  digraph:get_cycle(G,V) /= false],
	digraph:delete(G),
    oneof([witness(A) || Choices == []] ++
          [?LET({Cycle, Path}, (elements(Choices)),
                %%Cycle == [V] or [V,V1,V2,...,V]
                begin
                    Cycle2 = case Cycle of [X] -> [X, X]; _ -> Cycle end,
                    Prefix = build_witness(Path, Trans),
                    Loop = build_witness(Cycle2, Trans),
                    calc_and_expand_to_alpha(#witness{prefix=Prefix,
                                                      loop=Loop})
                end) || Choices /= []]).

calc_and_expand_to_alpha(#witness{prefix=Prefix, loop=Loop}) ->
    Alpha = extract_names(lists:flatten(Prefix) ++ lists:flatten(Loop)),
    NewPrefix = expand_labels(Alpha, Prefix),
    NewLoop = expand_labels(Alpha, Loop),
    #witness{loop=NewLoop, prefix=NewPrefix, alpha=Alpha}.

expand_labels(Alpha, Labels) ->
    lists:map(fun (Label) ->
					  Missing = Alpha -- extract_names(Label),
					  Label ++ Missing
			  end, Labels).

extract_names(Label) ->
    lists:usort(
	  lists:map(fun ({lnot, P}) -> P;
					(P) -> P
				end, Label)
	 ).

%% Generate a buchi automata
buchi() ->
    ?LET(Bl, (buchi_labeled()),
         (buchi:lbl2nonlbl(Bl))).

buchi(Alpha) ->
    ?LET(Bl, (buchi_labeled(Alpha)),
         (buchi:lbl2nonlbl(Bl))).

buchi_labeled() ->
    ?SIZED(Size,
           (?LET(Alpha, (alpha()), (buchi_labeled(Size, Alpha))))).

buchi_labeled(Alpha) ->
    ?SIZED(Size, (buchi_labeled(Size, Alpha))).

buchi_labeled(0, _Alpha) -> buchi:empty_labeled_buchi();
buchi_labeled(Size, Alpha) ->
    ?LET(NStates, (choose(1, Size)),
         begin
             States = lists:seq(1, NStates),
             ?LET({Accept, InitStates, Trans1},
                  {set(States), set(States), resize(Size * 5, list(elements(States)))},
                  (?LET({Trans2, Labels}, {vector(length(Trans1), elements(States)),
                                           vector(length(States), literals(Alpha))},
                        {lists:zip(States, Labels),
                         InitStates,
                         lists:usort(lists:zip(Trans1, Trans2)),
                         Accept})))
         end).

%% Non-empty buchi automata
buchi_ne() ->
    ?SUCHTHAT(B, (buchi()), (not buchi:is_empty(B))).

buchi_ne(Alpha) ->
    ?SUCHTHAT(B, (buchi(Alpha)), (not buchi:is_empty(B))).

%% Generate a LTL-formula
ltl_formula() ->
    ?SIZED(Size,
           (?LET(Alpha, (alpha()), (ltl_formula(Size, Alpha))))).

ltl_formula(Alpha) ->
    ?SIZED(Size, (ltl_formula(Size, Alpha))).

%% ltl_formula(0,Alpha) ->
%%  oneof([{lprop,elements(Alpha)},
%%         ltrue,
%%         lfalse]);
ltl_formula(0, Alpha) ->
    elements(Alpha);
ltl_formula(Size, Alpha) ->
    Smaller = ltl_formula(Size div 2, Alpha),
    MuchSmaller = ltl_formula(Size div 4, Alpha),
    oneof([ltl_formula(0, Alpha),
           ?LETSHRINK([Phi, Psi], [MuchSmaller, MuchSmaller], {land, Phi, Psi}),
           ?LETSHRINK([Phi, Psi], [MuchSmaller, MuchSmaller], {lor, Phi, Psi}),
           ?LETSHRINK([Phi], [Smaller], {next, Phi}),
           ?LETSHRINK([Phi], [Smaller], {eventually, Phi}),
           ?LETSHRINK([Phi], [Smaller], {always, Phi}),
           ?LETSHRINK([Phi], [Smaller], (?SHRINK({lnot, Phi},
                                                 (negate(Phi)))))]).

negate(ltrue) ->   [lfalse];
negate(lfalse) ->  [ltrue];
negate(_Phi) ->       [].

translations() ->
    [{"basic              ", fun basic_ltl2buchi:translate/1},
	 %% {"basic_red          ",
	 %% fun (Phi) -> buchi_reduce:reduce(buchi:ltl2buchi_basic(Phi)) end},
     %%      {"basic_red3         ",
     %%       fun (Phi) -> buchi:reduce3(buchi:ltl2buchi_basic(Phi)) end},
     %%      {"basic_red _rew     ",
     %%       fun (Phi) -> buchi:reduce(buchi:ltl2buchi_basic(ltl:ltl_rewrite(Phi))) end},
     %%      {"basic_red3_rew     ",
     %%       fun (Phi) -> buchi:reduce3(buchi:ltl2buchi_basic(ltl:ltl_rewrite(Phi))) end},
     %%      {"simple             ", fun buchi:ltl2buchi_simple/1},
     %%      {"simple_red         ",
     %%       fun (Phi) -> buchi:reduce(buchi:ltl2buchi_simple(Phi)) end},
     %%      {"simple_red3        ",
     %%       fun (Phi) -> buchi:reduce3(buchi:ltl2buchi_simple(Phi)) end},
     %%      {"simple_red _rew    ",
     %%       fun (Phi) -> buchi:reduce(buchi:ltl2buchi_simple(ltl:ltl_rewrite(Phi))) end},
     %%      {"simple_red3_rew    ",
     %%       fun (Phi) -> buchi:reduce3(buchi:ltl2buchi_simple(ltl:ltl_rewrite(Phi))) end},
     {"ltl2buchi          ", fun ltl2buchi:translate_norew/1},
     {"ltl2buchi_rew      ", fun ltl2buchi:translate/1}
     %%      {"ltl2buchi_rew      ",
     %%       fun (Phi) -> ltl2buchi:translate(ltl:ltl_rewrite(Phi)) end},
     %%      {"ltl2buchi_red      ",
     %%       fun (Phi) -> buchi:reduce(ltl2buchi:translate(Phi)) end},
     %%      {"ltl2buchi_red3     ",
     %%       fun (Phi) -> buchi:reduce3(ltl2buchi:translate(Phi)) end},
     %%      {"ltl2buchi          ",
     %%       fun (Phi) -> buchi:reduce(ltl2buchi:translate(ltl:ltl_rewrite(Phi))) end},
     %%      {"ltl2buchi_red2_rew ",
     %%       fun (Phi) -> buchi:reduce2(ltl2buchi:translate(ltl:ltl_rewrite(Phi))) end},
     %%      {"ltl2buchi_red3_rew ",
     %%       fun (Phi) -> buchi:reduce3(ltl2buchi:translate(ltl:ltl_rewrite(Phi))) end}
     , {"wring              ", fun wring_wrap:run/1}
     , {"java               ", fun ltl2buchi_wrap:run/1}
    ].

ltl2buchi() ->
    elements(translations()).

%%
%% Properties
%%

%% Test the wrappers
prop_wring_wrap() ->
    ?FORALL(
	   Phi, ltl_formula(),
	   begin
		   _B = wring_wrap:run(Phi),
		   ?WHENFAIL(
			  io:format("Wring fails for: ~p\n", [ltl:print_ltl(Phi)]),
			  true)
	   end).

prop_ltl2buchi_wrap() ->
    ?FORALL(
	   Phi, (ltl_formula()),
	   begin
		   _B = ltl2buchi_wrap:run(Phi),
		   ?WHENFAIL(
			  io:format("Java LTL2Buchi fails for: ~p\n", 
						[ltl:print_ltl(Phi)]),
			  true)
	   end).

%% Test of witness_for_buchi
prop_witness_for_buchi1() ->
    ?FORALL(
	   Alpha, alpha(),
	   ?FORALL(
		  Buchi, buchi_ne(Alpha),
		  ?FORALL(
			 W, witness_for_buchi(Buchi),
			 collect(W,
					 case is_witness_buchi(W, Buchi) of
						 true ->
							 W#witness.alpha -- Alpha == [];
						 false ->
							 true
					 end
					)))).


%%% The intersection of the automatas build from Phi and -Phi should be emtpy!
prop_test1_0() -> 
	prop_test1(fun ltl2buchi:translate/1,fun ltl2buchi_wrap:run/1).
prop_test1_0b() -> 
	prop_test1(fun ltl2buchi_wrap:run/1,fun ltl2buchi:translate/1).

prop_test1(B1, B2) ->
    ?FORALL(
	   Phi, (ltl_formula()),
	   begin
		   Bu1 = B1(Phi),
		   Bu2 = B2({lnot, Phi}),
		   Bu1Bu2 = buchi:intersection(Bu1, Bu2),
		   buchi:is_empty(Bu1Bu2)
	   end).

prop_test1() ->
    ?FORALL(
	   {{N1, B1}, {N2, B2}}, (noshrink({ltl2buchi(), ltl2buchi()})),
	   (?FORALL(Phi, (ltl_formula()),
				begin
					Bu1 = B1(Phi),
					Bu2 = B2({lnot, Phi}),
					Bu1Bu2 = buchi:intersection(Bu1, Bu2),
					?WHENFAIL((io:format("Property test1 failed with ~p(~p) and ~p(~p)\n" ++
										 "B1: ~w\nB2: ~w\n",
										 [N1, ltl:print_ltl(Phi), N2, ltl:print_ltl({lnot, Phi}),Bu1,Bu2])),
							  (buchi:is_empty(Bu1Bu2)))
				end))).



%% If we have Phi and -Phi, then every witness should be accepted by either
%% buchi(Phi) or buchi(-Phi)
%% Not really what test 2 in the paper says (that is too expensive, this is more
%% in the QuickCheck spirit!)
prop_test2_0() -> prop_test2(fun ltl2buchi:translate/1,fun ltl2buchi_wrap:run/1).
prop_test2_0b() -> prop_test2(fun ltl2buchi_wrap:run/1,fun ltl2buchi:translate/1).
prop_test2(B1, B2) ->
    ?FORALL(
	   Alpha, (alpha()),
	   ?FORALL(
		  {Phi, W}, {ltl_formula(Alpha), witness(Alpha)},
		  begin
			  Bu1 = B1(Phi),
			  Bu2 = B2({lnot, Phi}),
			  ?WHENFAIL(
				 io:format("Formula: ~p\nWitness: ~p\nBA1: ~p\n" ++
						   "BA2: ~p\nIWB1: ~p ===> IWB2: ~p\n" ++
						   "WB: ~p\nBu1 x WB: ~p\n",
						   [Phi, W, Bu1, Bu2, is_ltl_witness_buchi(W, Bu1),
							is_ltl_witness_buchi(W, Bu2), witness2buchi(W),
							buchi:ltl_intersection(witness2buchi(W), Bu1)]),
				 (is_ltl_witness_buchi(W, Bu1) orelse is_ltl_witness_buchi(W, Bu2)))
		  end)).

prop_test2() ->
    ?FORALL(
	   {{_N1, B1}, {_N2, B2}}, noshrink({ltl2buchi(), ltl2buchi()}),
       ?FORALL(
		  Alpha, (alpha()),
		  ?FORALL(
			 {Phi, W}, {ltl_formula(Alpha), witness(Alpha)},
			 begin
				 Bu1 = B1(Phi),
				 Bu2 = B2({lnot, Phi}),
				 ?WHENFAIL(
					io:format("Formula: ~p\nWitness: ~p\nBA1: ~p\n" ++
							  "BA2: ~p\nIWB1: ~p ===> IWB2: ~p\n" ++
							  "WB: ~p\nBu1 x WB: ~p\n",
							  [Phi, W, Bu1, Bu2, is_ltl_witness_buchi(W, Bu1),
							   is_ltl_witness_buchi(W, Bu2), witness2buchi(W),
							   buchi:ltl_intersection(witness2buchi(W), Bu1)]),
					(is_ltl_witness_buchi(W, Bu1) orelse is_ltl_witness_buchi(W, Bu2)))
			 end))).


%% This is cross compairsion of ltl2buchi translations, test 3 in the paper
%% Given Phi, generate Bu1 and Bu2 by using different translations.
%% Generate a Kripke structure (here a witness) and check that the 
%% Model-checking agree
prop_test3_0() -> prop_test2(fun ltl2buchi:translate/1,fun ltl2buchi_wrap:run/1).

prop_test3(B1, B2) ->
    ?FORALL(
	   Alpha, (alpha()),
	   ?FORALL(
		  Phi, (ltl_formula(Alpha)),
		  begin
			  Bu1 = B1(Phi),
			  Bu2 = B2(Phi),
			  ?FORALL(
				 W, (witness(Alpha)), %%witness_for_buchi(Bu1), 
				 ?WHENFAIL(io:format("Bu1: ~p\nBu2: ~p\nW: ~p\n", [Bu1, Bu2, W]),
						   (collect(is_ltl_witness_buchi(W, Bu1),
									is_ltl_witness_buchi(W, Bu1) ==
									is_ltl_witness_buchi(W, Bu2)))))
		  end)).

prop_test3() ->
    ?FORALL(
	   {{_N1, B1}, {_N2, B2}}, (noshrink({ltl2buchi(), ltl2buchi()})),
       ?FORALL(
		  Alpha, (alpha()),
		  ?FORALL(
			 Phi, (ltl_formula(Alpha)),
			 ?IMPLIES(wring_ok(Phi),
			 begin
				 Bu1 = B1(Phi),
				 Bu2 = B2(Phi),
				 ?FORALL(
					W, (witness(Alpha)), %%witness_for_buchi(Bu1),    
					?WHENFAIL(io:format("Bu1: ~p\nBu2: ~p\nW: ~p\n", [Bu1, Bu2, W]),
							  (collect(is_ltl_witness_buchi(W, Bu1),
									   is_ltl_witness_buchi(W, Bu1) ==
									   is_ltl_witness_buchi(W, Bu2)))))
			 end)))).

%% Properties for checking the reduce-function
prop_reduce_parts() ->
    ?FORALL(
	   A, alpha(),
	   %%    ?FORALL(B, buchi_ne(A),
	   ?FORALL(
		  L, ltl_formula(A),
		  begin
			  B = basic_ltl2buchi:translate(L),
			  B2 = buchi_reduce:remove_unnecessary_trans(B),
			  B3 = buchi_reduce:remove_non_reachable(B),
			  B4 = buchi_reduce:reduce_accept(B),
			  B5 = buchi_reduce:remove_fixed_formula_balls(B),
			  B6 = buchi_reduce:basic_bisim_red(B),
			  B7 = buchi_reduce:strong_fair_sim_red(B),
			  B8 = buchi_reduce:remove_unnecessary_states_simp(B),
			  B9 = buchi_reduce:reduce(B),
			  ?ALWAYS(10,
					  ?FORALL(
						 W, witness(A),
						 begin
							 Bools = [is_ltl_witness_buchi(W,Bx) 
									  || Bx <- [B,B2,B3,B4,B5,B6,B7,B8,B9]],
							 ?WHENFAIL(
								io:format("Results: ~p\n",[Bools]),
								length(lists:usort(Bools)) == 1)
						 end))
                    end)).

prop_check_reduce(F) ->
    ?FORALL(
	   A, alpha(),
       ?FORALL(
		  B1, buchi(A),
		  ?FORALL(
			 W, witness(A),
			 begin
				 B2 = F(B1),
				 ?WHENFAIL(
					io:format("~p reduced to \n~p\nUsed witness ~p (B1: ~p, B2: ~p)\n",
							  [B1, B2, W, is_ltl_witness_buchi(W, B1),
							   is_ltl_witness_buchi(W, B2)]),
					(is_ltl_witness_buchi(W, B1) ==
					 is_ltl_witness_buchi(W, B2)))
			 end))).

prop_check_reduce2(F) ->
    ?FORALL(
	   A, alpha(),
       ?FORALL(
		  Phi, ltl_formula(A),
          ?FORALL(
			 W, witness(A),
			 begin
				 %%            B1 = ltl2buchi:translate(Phi),
				 B1 = basic_ltl2buchi:translate(Phi),
				 %%        B2 = buchi:basic_bisim_red(B1),
				 B2 = F(B1),
				 %%            B2 = buchi:reduce3(B1),
				 ?WHENFAIL(
					io:format("~p reduced to \n~p\nUsed witness ~p (B1: ~p, B2: ~p)\n",
							  [B1, B2, W, is_ltl_witness_buchi(W, B1),
							   is_ltl_witness_buchi(W, B2)]),
					(is_ltl_witness_buchi(W, B1) ==
					 is_ltl_witness_buchi(W, B2)))
			 end))).

prop_check_rewrite() ->
    ?FORALL(
	   L,ltl_formula(),
	   begin
		   Bu1 = basic_ltl2buchi:translate(L),
		   Bu2 = basic_ltl2buchi:translate(ltl_rewrite:rewrite(ltl:lnot(L))),
		   Bu3 = basic_ltl2buchi:translate(ltl_rewrite:rewrite(L)),
		   Bu4 = basic_ltl2buchi:translate(ltl:lnot(L)),
		   Bu1Bu2 = buchi:intersection(Bu1, Bu2),
		   Bu3Bu4 = buchi:intersection(Bu3, Bu4),
		   ?WHENFAIL(
			  io:format("Property failed with ~p and ~p\n",
						[ltl:print_ltl(L), 
						 ltl:print_ltl({lnot, L})]),
			  (buchi:is_empty(Bu1Bu2) andalso buchi:is_empty(Bu3Bu4)))
	   end).


%% lbl2nonlbl ?? How to test in a meaningful way?? 
%% Correct by inspection ;-)

%% degeneralized
%% a degeneralized BA accepts the same witnesses as
%% the original generalized automata does

%% intersection
%% 1. B1xB2 accepts the same witnesses as B2xB1
%% 2. If B1 <= w & B2 <= w then B1xB2 <= w
%% 3  generate w s.t. B1xB2 <=w then B1 <= w & B2 <= w
prop_intersection_t1() ->
    ?FORALL(
	   A, alpha(),
	   ?FORALL(
		  {B1, B2}, {buchi_ne(A), buchi_ne(A)},
		  begin
			  B1B2 = buchi:intersection(B1, B2),
			  B2B1 = buchi:intersection(B2, B1),
			  ?FORALL(
				 W, witness_for_buchi(A, B1B2),
				 (collect(is_witness_buchi(W, B1B2),
						  is_witness_buchi(W, B1B2) ==
						  is_witness_buchi(W, B2B1))))
		  end)).

prop_intersection_t1_2() ->
    ?FORALL(
	   A, alpha(),
	   ?FORALL(
		  {B1, B2}, {buchi_ne(A), buchi_ne(A)},
		  begin
			  B1B2 = buchi:intersection(B1, B2),
			  B2B1 = buchi:intersection(B2, B1),
			  ?ALWAYS(10,
					  ?FORALL(
						 W, witness(A),
						 (collect(is_witness_buchi(W, B1B2),
								  is_witness_buchi(W, B1B2) ==
								  is_witness_buchi(W, B2B1)))))
		  end)).

prop_intersection_t2() ->
    ?FORALL(
	   A, alpha(),
	   ?FORALL(
		  {B1, B2}, {buchi_ne(A), buchi_ne(A)},
		  begin
			  B1B2 = buchi:intersection(B1, B2),
			  ?FORALL(
				 W, witness_for_buchi(A, B1),
				 ?IMPLIES(
					is_witness_buchi(W, B1),
					begin
						IWB2 = is_witness_buchi(W, B2),
						measure(len_witness, length(W#witness.prefix) + length(W#witness.loop),
								collect(IWB2,
										?WHENFAIL(
										   io:format("~p and ~p == ~p\nB1B2: ~p\n",
													 [is_witness_buchi(W, B1), is_witness_buchi(W, B2),
													  is_witness_buchi(W, B1B2), B1B2]),
										   (IWB2 == is_witness_buchi(W, B1B2)))))
					end))
		  end)).

prop_intersection_t3() ->
    ?FORALL(
	   A, alpha(),
	   ?FORALL(
		  {B1, B2}, {buchi_ne(A), buchi_ne(A)},
		  begin
			  B1B2 = buchi:intersection(B1, B2),
			  ?FORALL(
				 W, witness_for_buchi(A, B1B2),
				 ?IMPLIES(is_witness_buchi(W, B1B2),
						  measure(len_witness, length(W#witness.prefix) + length(W#witness.loop),
								  is_witness_buchi(W, B2) andalso
								  is_witness_buchi(W, B1))))
		  end)).

%% A property to check the ltl_rewrite 
prop_ltlrewrite() ->
    ?FORALL(
	   Alpha, alpha(),
	   ?FORALL({Phi, W}, {ltl_formula(Alpha), witness(Alpha)},
			   (is_witness_ltl(W, Phi) ==
				is_witness_ltl(W, ltl_rewrite:rewrite(Phi))))).

%% Some props to check the reduce_group function, it simplifies
%% a set of transition lables...
prop_reduce_group() ->
    ?FORALL(
	   Alpha, alpha(),
	   ?FORALL(
		  Group, (list1(literals(Alpha))),
		  begin
			  Group1 = lists:usort(Group),
			  Group2 = buchi:reduce_group(Group1),
			  ?FORALL(
				 Test, (label(Alpha)),
				 ?WHENFAIL(
					io:format("Grp: ~p reduced to ~p\nFails for test: ~p (~p :: ~p)\n",
							  [Group1, Group2, Test,
							   tr_match(Test, Group1), tr_match(Test, Group2)]),
					(tr_match(Test, Group1) == tr_match(Test, Group2) andalso
					 length(Group2) =< length(Group1))))
		  end)).

tr_match(_Test,[]) ->
    false;
tr_match(Test,[Tr | Trs]) ->
    case Tr -- Test of
        [] -> true;
        _ -> tr_match(Test,Trs)
    end.

%% Size optimization properties...
prop_compare_size() ->
    ?FORALL(
	   Phi, ltl_formula(),
	   ?IMPLIES(wring_ok(Phi),
				begin
					Trs = [{N, F(Phi)} || {N, F} <- translations()],
					nested_measure(Trs, true)
				end)).

nested_measure([],P) -> P;
nested_measure([{Name,Buchi} | Trs],P) ->
    erlang:apply(fun eqc:measure/3,[Name,buchi_utils:size_of(Buchi),nested_measure(Trs,P)]).

wring_ok(Phi) ->
    case catch wring_wrap:run(Phi) of
        {'EXIT',_} -> false;
        _ -> true
    end.

%% Property to find degenerate cases
prop_discover_diffsize() ->
    ?FORALL(
	   Phi, (ltl_formula()),
	   begin
		   B1 = ltl2buchi_wrap:run(Phi),
		   B2 = ltl2buchi:translate(Phi),
		   ?WHENFAIL(
			  io:format("Formula ~p is translated into\n~p \n" ++ 
						"which is much smaller " ++
						"(~p vs ~p) than:\n~p\n",
						[ltl:pp(Phi, normal), B1, 
						 buchi_utils:size_of(B1), buchi_utils:size_of(B2), B2]),
			  buchi_utils:size_of(B1) + 3 > buchi_utils:size_of(B2))
	   end).

prop_discover_diffsize2() ->
    ?FORALL(
	   Phi, (ltl_formula()),
	   begin
		   B1 = ltl2buchi_wrap:run(Phi),
		   B2 = ltl2buchi:translate(Phi),
		   ?WHENFAIL(
			  io:format("Formula ~p is translated into\n~p \n" ++ 
						"which is much *bigger* " ++
						"(~p vs ~p) than:\n~p\n",
						[ltl:pp(Phi, normal), B1, 
						 buchi_utils:size_of(B1), buchi_utils:size_of(B2), B2]),
			  buchi_utils:size_of(B2) + 3 > buchi_utils:size_of(B1))
	   end).


%%%
%% Testing the parser
%%%

prop_parse() ->
	?FORALL({Ltl,Style}, {ltl_formula(),elements([normal,java,wring])},
			begin
				ltl_parse:string(ltl:pp(Ltl,Style)),
				?WHENFAIL( io:format("Formula: ~s\n",[ltl:pp(Ltl,Style)]), true)
			end).

prop_parse2() ->
	?FORALL({Ltl,Style}, {ltl_formula(),elements([normal,java,wring])},
			begin
				S1 = ltl:pp(Ltl,Style),
				Ltl2  = ltl_parse:string(S1),
				?WHENFAIL( io:format("Formula: ~s\n",[ltl:pp(Ltl,Style)]), Ltl == Ltl2)
			end).


%%
%% Functions
%%

is_witness_buchi(W,B) ->
    WB = witness2buchi(W),
    %%     not buchi:is_empty(buchi:ltl_intersection(WB,B)).
    not buchi:is_empty(buchi:intersection(WB,B)).

is_ltl_witness_buchi(W,B) ->
    WB = witness2buchi(W),
    not buchi:is_empty(buchi:ltl_intersection(WB,B)).

witness2buchi(#witness{prefix = Prf, loop = Lp}) ->
    States = lists:seq(1,length(Prf)+length(Lp)),
    Trans = [{N-1,N,Lbl} || 
                {N,Lbl} <- lists:zip(tl(States),Prf++init(Lp))],
    {States,[1],Trans ++ [{lists:last(States),1 + length(Prf),lists:last(Lp)}],
     lists:seq(1 + length(Prf),length(States))}.

init(Lst) ->
    lists:reverse(tl(lists:reverse(Lst))).

build_witness([],_Tr) ->
    [];
build_witness([_X],_Tr) ->
    [];
build_witness([X,Y | Zs],Tr) ->
    [find_tr(X,Y,Tr) | build_witness([Y|Zs],Tr)].

find_tr(X,Y,[{X,Y,St} | _Tr]) ->
    lists:filter(fun(P) -> case P of
                               {lnot,_} -> false;
                               _ -> true
                           end
                 end,St);
find_tr(X,Y,[_ | Tr]) ->
    find_tr(X,Y,Tr).

%% spawned_buchi2digraph(B = {_States,InitStates,_Trans,Accept}) ->
%%     %% Running out of ets-tables...
%%     Self = self(),
%%     spawn(fun() ->
%%                   {ok,G} = buchi:buchi2digraph(B),
%%                   Reachable = digraph_utils:reachable(InitStates,G),
%%                   Choices = [ {digraph:get_cycle(G,V),digraph:get_path(G,1,V)} || 
%%                                 V <- Accept,
%%                                 lists:member(V,Reachable),
%%                                 digraph:get_cycle(G,V) /= false],
%%                   digraph:delete(G),
%%                   Self ! Choices
%%           end),
%%     receive
%%         X -> X
%%     end.

remove_release({release,Phi1,Phi2}) ->
    {lnot,{until,
           {lnot,remove_release(Phi1)},
           {lnot,remove_release(Phi2)}}};
remove_release({Op,Phi1,Phi2}) ->
    {Op,remove_release(Phi1),remove_release(Phi2)};
remove_release({Op,Phi}) ->
    {Op,remove_release(Phi)};
remove_release(Phi) ->
    Phi.

is_witness_ltl(#witness{prefix = Prf,loop = Lp},Phi) ->
    SimpPhi = remove_release(ltl2buchi:simplify(Phi)),
    Subs = ltl_utils:subformulas(SimpPhi),
    Res = is_witness_ltl(lists:zip(lists:seq(1,length(Prf++Lp)),Prf ++ Lp),
                         length(Prf)+1,lists:reverse(Subs),[]),
    %%  io:format("Subs: ~p\nRes: ~p\n",[Subs,Res]),
    lists:member({1,SimpPhi},Res).

is_witness_ltl(_Ss, _Lp, [], Res) ->
    Res;
is_witness_ltl(Ss, Lp, [Sub| Subs], Res) ->
    ResAdd =
        case Sub of
            ltrue ->
                [{S, Sub} || {S, _} <- Ss];
            lfalse ->
                [];
            {lprop, _X} ->
                [{S, Sub} || {S, Lbl} <- Ss, lists:member(Sub, Lbl)];
            {lnot, Phi} ->
                [{S, Sub} || {S, _} <- Ss, not lists:member({S, Phi}, Res)];
            {lor, Phi1, Phi2} ->
                [{S, Sub} || {S, _} <- Ss,
                             lists:member({S, Phi1}, Res) orelse
                                 lists:member({S, Phi2}, Res)];
            {land, Phi1, Phi2} ->
                [{S, Sub} || {S, _} <- Ss,
                             lists:member({S, Phi1}, Res) andalso
                                 lists:member({S, Phi2}, Res)];
            {next, Phi} ->
                Next = fun (X) -> case length(Ss) > X of
                                      true -> X + 1;
                                      false -> Lp
                                  end
                       end,
                [{S, Sub} || {S, _} <- Ss,
                             lists:member({Next(S), Phi}, Res)];
            {until, Phi1, Phi2} ->
                handle_until(Sub, Phi1, Phi2, [], [], Res, Ss, Lp)
        end,
    is_witness_ltl(Ss, Lp, Subs, Res ++ ResAdd).

handle_until(Phi,_Phi1,_Phi2,Mark,ResAdd,_Res,[],Lp)->
    case lists:member({Lp,Phi},ResAdd) of
        true -> ResAdd ++ [{S2,Phi} || S2 <- Mark];
        false -> ResAdd
    end;
handle_until(Phi,Phi1,Phi2,Mark,ResAdd,Res,[{S,_} | Ss],Lp) ->
    case lists:member({S,Phi2},Res) of
        true ->
            NewResAdd = ResAdd ++ [{S,Phi} | [{S2,Phi} || S2 <- Mark]],
            handle_until(Phi,Phi1,Phi2,[],NewResAdd,Res,Ss,Lp);
        false ->
            case lists:member({S,Phi1},Res) of
                true ->
                    handle_until(Phi,Phi1,Phi2,[S|Mark],ResAdd,Res,Ss,Lp);
                false ->
                    handle_until(Phi,Phi1,Phi2,[],ResAdd,Res,Ss,Lp)
            end
    end.



