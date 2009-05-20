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

-module(buchi).

%% -export([is_labeled/1,is_nonlabeled/1,is_generalized/1,size_of/1,
%% 	 is_empty/1,intersection/2,reduce/1,remove_non_reachable/1,		 
%% 	 reachable_loop_states/1,ltl_intersection/2,reachable/2,
%% 	 lbl2nonlbl/1, %%nonlbl2lbl/1,
%% 	 buchi2digraph/1,remove_subsets/1,
%% 	 empty_buchi/0,empty_labeled_buchi/0,
%%      degeneralize/1,
%% 	 ltl2buchi_basic/1, basic_bisim_red/1, btest3/0,
%% 	 ltl2buchi_simple/1]).
-compile(export_all).

%% General types
-type(literal() :: {lprop,atom()} | {lnot,{lprop,atom()}}).
-type(label()   :: [literal()]).

-type(state()   :: integer()).
-type(lbl_state() :: {state(),label()}).

-type(states()    :: [state()]).
-type(lbl_states() :: [lbl_state()]).

-type(transition() :: {state(),state()}).
-type(transitions() :: [transition()]).
-type(lbl_transition() :: {state(),state(),label()}).
-type(lbl_transitions() :: [lbl_transition()]).

-type(accepts()     :: states()).
-type(gen_accepts() :: [accepts()]).

-type(gen_lbl_buchi() :: {lbl_states(),states(),transitions(),gen_accepts()}).
-type(lbl_buchi() :: {lbl_states(),states(),transitions(),accepts()}).
-type(gen_non_lbl_buchi() :: {states(),states(),lbl_transitions(),gen_accepts()}).
-type(non_lbl_buchi() :: {states(),states(),lbl_transitions(),accepts()}).

-type(gen_buchi() :: gen_lbl_buchi() | gen_non_lbl_buchi()).
-type(non_gen_buchi() :: lbl_buchi() | non_lbl_buchi()).

-type(labeled_buchi() :: gen_lbl_buchi() | lbl_buchi()).
-type(non_labeled_buchi() :: gen_non_lbl_buchi() | non_lbl_buchi()).

-type(buchi() :: labeled_buchi() | non_labeled_buchi()).

%%
%% Buchi recognizers
%%
												% True if the BA has its labels in the states
-spec(is_labeled/1::(buchi())->bool()).
is_labeled({_,_,[{_,_} | _],_}) ->
    true;
is_labeled({[{_,_} | _],_,_,_}) ->
    true;
is_labeled({[],_,[],_}) ->
    true;
is_labeled(_) ->
    false.

-spec(is_nonlabeled/1::(buchi())->bool()).
is_nonlabeled({_,_,[{_,_,_} | _],_}) ->
    true;
is_nonlabeled({[X|_],_,[],_}) when is_integer(X) ->
    true;
is_nonlabeled({[],_,[],_}) ->
    true;
is_nonlabeled(_) ->
    false.

												% True if The BA is generalized
-spec(is_generalized/1::(buchi())->bool()).
is_generalized({_,_,_,[Ac | _]}) ->
    is_list(Ac);
is_generalized(_) ->
    false.

												% Returns a (bad) measure of the size of the BA
-spec(size_of/1::(buchi())->integer()).
size_of({States,_InitStates,Trans,_Accepts}) ->
    length(States) + length(Trans).


%%
%% Main functions on BA
%%

												% The empty BA
-spec(empty_buchi/0::()->(non_labeled_buchi())).
empty_buchi() -> {[1],[1],[],[]}.
-spec(empty_labeled_buchi/0::()->(labeled_buchi())).
empty_labeled_buchi() -> {[],[],[],[]}.

												% ltl2buchi translation basic (core algorithms in ltl-module)
ltl2buchi_basic(Phi) ->
    B0 = basic_ltl2buchi:basic_ltl_to_buchi(Phi),
    degeneralize(lbl2nonlbl(B0)).

ltl2buchi_simple(Phi) ->
    B0 = simple_ltl2buchi:simple_to_buchi(Phi),
    degeneralize(lbl2nonlbl(B0)).

%% Empty check
-spec(is_empty/1::(buchi())->bool()).
is_empty(B = {_States,_InitStates,_Trans,_Accept}) ->
    case reachable_loop_states(B) of
		[] -> true;
		_ -> false
    end.

-spec(reachable_loop_states/1::(non_lbl_buchi())->states()).
reachable_loop_states(B = {_States,InitStates,_Trans,Accept}) ->
    {ok,G} = buchi2digraph(B),
    Reachable = digraph_utils:reachable(InitStates,G),
    Res = [ V || V <- Accept,
				 lists:member(V,Reachable),
				 digraph:get_cycle(G,V) /= false],
	digraph:delete(G),
	Res.


												% Computes the product/intersection of two BA's,
												% the result is a non-generalized, non-labeled BA.
-spec(intersection/2::(buchi(),buchi())->non_lbl_buchi()).
intersection(B1,B2) ->
    intersection2(degeneralize(B1),degeneralize(B2)).

intersection2(_B1 = {_States1, InitStates1, Trans1, Accept1},
	      _B2 = {States2, InitStates2, Trans2, Accept2}) ->
    AllInitStates =
	[{S1, S2, 1} || S1 <- InitStates1, S2 <- InitStates2],
    AllAccept =
	[{F1, S2, 1} || F1 <- Accept1, S2 <- States2],
    AllTrans =
	[{{S1_1, S2_1, 1}, {S1_2, S2_2, 1}, St1}
	 || {S1_1, S1_2, St1} <- Trans1,
	    {S2_1, S2_2, St2} <- Trans2,
	    St1 == St2,
	    not lists:member(S1_1, Accept1)] ++
	  [{{S1_1, S2_1, 1}, {S1_2, S2_2, 2}, St1}
	   || {S1_1, S1_2, St1} <- Trans1,
	      {S2_1, S2_2, St2} <- Trans2,
	      St1 == St2,
	      lists:member(S1_1, Accept1)] ++
	    [{{S1_1, S2_1, 2}, {S1_2, S2_2, 2}, St1}
	     || {S1_1, S1_2, St1} <- Trans1,
		{S2_1, S2_2, St2} <- Trans2,
		St1 == St2,
		not lists:member(S2_1, Accept2)] ++
	      [{{S1_1, S2_1, 2}, {S1_2, S2_2, 1}, St1}
	       || {S1_1, S1_2, St1} <- Trans1,
		  {S2_1, S2_2, St2} <- Trans2,
		  St1 == St2,
		  lists:member(S2_1, Accept2)],
    Reachable = lists:usort(reachable(AllTrans, AllInitStates)),
    case Reachable of
      [] -> {[], [], [], []};
      _ ->
	  StMap = lists:zip(lists:seq(1, length(Reachable)), Reachable),
	  Trans = [{stmap(S1, StMap), stmap(S2, StMap), St} || {S1, S2, St} <- AllTrans,
							       lists:member(S1, Reachable)],
	  Accept = [stmap(S, StMap) || S <- AllAccept,
				       lists:member(S, Reachable)],
	  States = lists:seq(1, length(Reachable)),
	  InitStates = [stmap(S, StMap) || S <- AllInitStates],
	  {States, InitStates, Trans, Accept}
    end.

%% LTL intersection, 
%% The first BA is a System model (or an automata generated
%% from a witness) and the second BA is generated from an 
%% LTL formula. Does this operation have a proper name!??
-spec(ltl_intersection/2::(buchi(),buchi())->non_lbl_buchi()).
ltl_intersection(B1,B2) ->
    ltl_intersection2(degeneralize(B1),degeneralize(B2)).

ltl_intersection2(_B1 = {_States1,InitStates1,Trans1,Accept1},
				  _B2 = {States2,InitStates2,Trans2,Accept2}) ->
    AllInitStates = 
		[{S1,S2,1} || S1 <- InitStates1, S2 <- InitStates2],
    AllAccept =
		[{F1,S2,1} || F1 <- Accept1, S2 <- States2],
    AllTrans = 
		[ {{S1_1,S2_1,1},{S1_2,S2_2,1},St2} || 
			{S1_1,S1_2,St1} <- Trans1, 
			{S2_1,S2_2,St2} <- Trans2, 
			is_sat(St2,St1),
			not lists:member(S1_1,Accept1) ] ++
		[ {{S1_1,S2_1,1},{S1_2,S2_2,2},St2} || 
			{S1_1,S1_2,St1} <- Trans1, 
			{S2_1,S2_2,St2} <- Trans2, 
			is_sat(St2,St1),
			lists:member(S1_1,Accept1) ] ++
		[ {{S1_1,S2_1,2},{S1_2,S2_2,2},St2} || 
			{S1_1,S1_2,St1} <- Trans1, 
			{S2_1,S2_2,St2} <- Trans2, 
			is_sat(St2,St1),
			not lists:member(S2_1,Accept2) ] ++
		[ {{S1_1,S2_1,2},{S1_2,S2_2,1},St2} || 
			{S1_1,S1_2,St1} <- Trans1, 
			{S2_1,S2_2,St2} <- Trans2, 
			is_sat(St2,St1),
			lists:member(S2_1,Accept2) ],
    Reachable = lists:usort(reachable(AllTrans,AllInitStates)),
    case Reachable of
		[] -> {[],[],[],[]};
		_ ->
			StMap = lists:zip(lists:seq(1,length(Reachable)),Reachable),
			Trans = [{stmap(S1,StMap),stmap(S2,StMap),St} || {S1,S2,St} <- AllTrans,
															 lists:member(S1,Reachable)],

			Accept = [ stmap(S,StMap) || S <- AllAccept,
										 lists:member(S,Reachable)],
			States = lists:seq(1,length(Reachable)),
			InitStates = [ stmap(S,StMap) || S <- AllInitStates],
			{States,InitStates,Trans,Accept}
    end.


%% Remove non reachable states
-spec(remove_non_reachable/1::(buchi())->buchi()).
remove_non_reachable(B = {States,InitStates,Trans,_Accept}) ->
    Reachable = reachable(Trans,InitStates),
    RStates = case is_labeled(B) of
				  true -> [ {S,St} || {S,St} <- States, 
									  not lists:member(S,Reachable)];
				  false -> States -- Reachable
			  end,
    remove(RStates,B).   

%% reduce a non-labeled buchi automata
-spec(reduce3/1::(non_labeled_buchi())->non_lbl_buchi()).
reduce3(B) ->
	B1 = normalize_trans(degeneralize(make_unlabeled(B))),
	reduce3_(B1).

reduce3_(B) ->
	B0 = remove_unnecessary_trans(B),
	B1 = remove_non_reachable(B0),
 	B11 = reduce_accept(B1),
	B2 = remove_never_accept(B11),
	%%  	B3 = remove_fixed_formula_balls(B2),
	B4 = basic_bisim_red(B2),
	B5 = strong_fair_sim_red(B4),
	case size_of(B5) < size_of(B) of
		true ->
			reduce3_(B5);
		false ->
			B5
	end.

-spec(reduce2/1::(non_labeled_buchi())->non_lbl_buchi()).
reduce2(B) ->
	B1 = normalize_trans(degeneralize(make_unlabeled(B))),
	reduce2_(B1).

reduce2_(B) ->
	B0 = remove_unnecessary_trans(B),
	B1 = remove_non_reachable(B0),
 	B11 = reduce_accept(B1),
	B2 = remove_never_accept(B1),
 	B3 = remove_fixed_formula_balls(B2),
 	B4 = basic_bisim_red(B3),
	B5 = strong_fair_sim_red(B4),
	case size_of(B5) < size_of(B) of
		true ->
			reduce2_(B5);
		false ->
			B5
	end.

-spec(reduce/1::(non_labeled_buchi())->non_lbl_buchi()).
reduce(B) ->
	B1 = normalize_trans(degeneralize(make_unlabeled(B))),
	reduce1(B1).

reduce1(B) ->
	B0 = remove_unnecessary_trans(B),
	B1 = remove_non_reachable(B0),
	B2 = remove_never_accept(B1),
 	B3 = remove_fixed_formula_balls(B2),
 	B4 = basic_bisim_red(B3),
	case size_of(B4) < size_of(B) of
		true ->
			reduce1(B4);
		false ->
			B4
	end.

reduce_lbl(B = {States,InitStates,Trans,_Accept}) ->
    case is_labeled(B) of
		false ->
			io:format("*WARNING*: Reduce can only be applied to labeled automata\n"),
			B;
		true ->
			case removable(lists:filter(fun({S,_}) -> 
												not lists:member(S,InitStates) 
										end,States),
						   Trans) of
				[] -> B;
				Rem -> reduce(remove(Rem,B))
			end
    end.


%% Normalize transitions, sort labels and remove true from labels
-spec(normalize_trans/1::(non_lbl_buchi())->non_lbl_buchi()).
normalize_trans({States,InitStates,Trans,Accept}) ->
	Trans1 = [ {S1,S2,lists:usort(St -- [ltrue,{lnot,lfalse}])} 
			   || {S1,S2,St} <- Trans],
	{States,InitStates,lists:usort(Trans1),Accept}.

%% Remove unnecessary transitions,
%% Sx -- [] --> Sy and Sx -- [a,b] --> Sy 
%% is reduced to only Sx -- [] --> Sy
%% and
%% Sx -- [a,b] --> Sy and Sx -- [a,!b] --> Sy
%% is reduced to only Sx -- [a] --> Sy, etc
-spec(remove_unnecessary_trans/1::(non_lbl_buchi())->non_lbl_buchi()).
remove_unnecessary_trans(B = {_,_,[],_}) ->
	B;
remove_unnecessary_trans({States,InitStates,Trans,Accept}) ->
	Trans1 = remove_unnecessary_trans1(Trans,hd(Trans),[]),
 	{States,InitStates,Trans1,Accept}.

-spec(remove_unnecessary_trans1/3 :: 
	  (lbl_transitions(),lbl_transition(),[label()]) -> lbl_transitions()).				 
remove_unnecessary_trans1([],Tr,Grp) ->
	analyze_group(Tr,Grp);
remove_unnecessary_trans1([{X,Y,Lbl} | Trs],Tr = {X,Y,_},Grp) ->
	remove_unnecessary_trans1(Trs,Tr,[Lbl | Grp]);
remove_unnecessary_trans1([Tr = {_,_,Lbl} | Trs], Tr2, Grp) ->
	analyze_group(Tr2,Grp) ++ remove_unnecessary_trans1(Trs,Tr,[Lbl]).


-spec(analyze_group/2::(lbl_transition(),[label()])->lbl_transitions()).
analyze_group({X,Y,_},Grp) ->	
	[{X,Y,Lbl} || Lbl <- reduce_group(Grp)].

-spec(reduce_group/1::([label()]) -> [label()]).
reduce_group(Grp) ->
	case lists:member([],Grp) of
		true -> [[]]; %Only the TRUE transition
		false ->
			Grp1 = simp(Grp),
			Remove = [Lbl2  
					  ||	Lbl1 <- Grp1,
							Lbl2 <- Grp1,
							Lbl1 /= Lbl2,
							Lbl1 -- Lbl2 == []],
			Grp1 -- Remove
	end.

-spec(simp/1::([label()]) -> [label()]).
simp(Grp) ->
	Grp1 = lists:usort(simp_2(simp_1(Grp))),
	case Grp1 == Grp of
		true -> Grp;
		false -> simp(Grp1)
	end.	

-spec(simp_1/1::([label()]) -> [label()]).
simp_1(Grp) ->
	simp_1_(Grp,Grp).
-spec(simp_1_/2::([label()],[label()]) -> [label()]).
simp_1_(Grp,[]) ->
	Grp;
simp_1_(Grp,[Lbl | Grp2]) ->
	case simp_1__(Grp,Lbl,Grp2) of
		false ->
			simp_1_(Grp,Grp2);
		NewGrp ->
			simp_1(NewGrp)
	end.
-spec(simp_1__/3::([label()],label(),[label()]) -> false | [label()]).
simp_1__(_,_,[]) ->
	false;
simp_1__(Grp,Lbl,[Lbl2 | Grp2]) ->
	case simp_1(Lbl,Lbl2) of
		false ->
			simp_1__(Grp,Lbl,Grp2);
		NewLbl -> (Grp -- [Lbl,Lbl2]) ++ [NewLbl]
	end.

simp_1(Lbl1, Lbl2) ->
    case Lbl1 -- Lbl2 of
      [X] -> case Lbl2 -- Lbl1 of
	       [Y] -> case X == ltl:negate(Y) of
			true -> Lbl1 -- [X];
			false -> false
		      end;
	       _ -> false
	     end;
      _ -> false
    end.

-spec(simp_2/1::([label()]) -> [label()]).
simp_2(Grp) ->
	Singletons = [S || S = [_] <- Grp],
	[lists:foldl(fun([S],L) -> simp_2(S,L) end, Lbl,Singletons) || Lbl <- Grp].
-spec(simp_2/2::(literal(),label()) -> [label()]).

simp_2(X, Lbl) ->
    case lists:member(ltl:negate(X), Lbl) of
      true -> Lbl -- [ltl:negate(X)];
      false -> Lbl
    end.

%% simp_3(Lbl1,Lbl2,Grp) ->
%% 		case overlap(Lbl1,Lbl2) of
%% 				false -> Grp;
%% 				Lbl -> 
%% 						case lists:member(lists:usort(Lbl),Grp) of
%% 								true -> Grp -- Lbl;
%% 								false -> Grp
%% 						end
%% 		end.

test1() -> [[{lprop,a},{lprop,b}],[{lprop,b}]].
test2() -> [[{lprop,a},{lnot,{lprop,b}}],[{lprop,a},{lprop,b}]].
test3() -> [[{lprop,a},{lnot,{lprop,b}},{lnot,{lprop,c}}],[{lprop,b}],[{lprop,c}]].
test4() -> [[{lprop,a},{lnot,{lprop,b}}],[{lprop,b},{lprop,c}]].
test5() -> [[{lprop,a},{lnot,{lprop,b}}],[{lprop,b},{lprop,c}],[{lprop,a},{lprop,c}]].
test6() -> [[{lprop,a},{lnot,{lprop,b}}],[{lprop,a},{lprop,b}],[{lprop,b}]].



%%%% end remove_unnecessary_trans
-spec(reduce_accept/1 :: (non_lbl_buchi()) -> non_lbl_buchi()).
reduce_accept(B = {States,InitStates,Trans,Accept}) ->
	{ok,G} = buchi2digraph(B),
	InCycle = lists:flatten(digraph_utils:cyclic_strong_components(G)),
	NotInCycle = Accept -- InCycle,
	digraph:delete(G),
	{States,InitStates,Trans,Accept -- NotInCycle}.

-spec(remove_never_accept/1 :: (non_lbl_buchi()) -> non_lbl_buchi()).
remove_never_accept(B = {States,_InitStates,_Trans,Accept}) ->
	{ok,G} = buchi2digraph(B),
												%Strongly connected components containing an accepting state
	SCs = lists:filter(fun(SC) ->
							   SC -- Accept /= SC
					   end,digraph_utils:cyclic_strong_components(G)),
	RemCands = States -- lists:flatten(SCs),
	Rem = [ S || S <- RemCands,
				 not reaches_accept(digraph_utils:reachable([S],G),SCs)],
	%% 	io:format("SCs: ~p\nRemCands: ~p\nRem: ~p\nReach:~p\n",
	%%            [SCs,RemCands,Rem,digraph_utils:reachable([hd(RemCands)],G)]),
	digraph:delete(G),
	remove(Rem,B).

-spec(reaches_accept/2 :: (states(),[states()]) -> bool()).

reaches_accept(_Reachable, []) ->
    false;
reaches_accept(Reachable, [SC| SCs]) ->
    case Reachable -- SC /= Reachable of
      true -> true;
      false -> reaches_accept(Reachable, SCs)
    end.


-spec(remove_fixed_formula_balls/1 :: (non_lbl_buchi()) -> non_lbl_buchi()).
remove_fixed_formula_balls(B = {_States,_InitStates,Trans,_Accept}) ->
	{ok,G} = buchi2digraph(B),
	SCs = lists:filter(fun({_,_}) -> true; (_) -> false end,
					   lists:map(fun(X) ->
										 is_fixed_formula_ball(X,Trans)
								 end,digraph_utils:cyclic_strong_components(G))),
	%% 	io:format("B: ~p\n ==> SCs: ~p\n",[B,SCs]),
	digraph:delete(G),
	collapse_balls(SCs,B).


-spec(is_fixed_formula_ball/2 :: 
	  (states(),lbl_transitions()) -> {states(),label()} | bool()).
is_fixed_formula_ball([_X],_Trans) -> false;
is_fixed_formula_ball(SC,Trans) ->
	case is_ball(SC,Trans) of
		true ->
			Lbls = lists:usort([ St || {S1,S2,St} <- Trans,
									   lists:member(S1,SC),
									   lists:member(S2,SC)]),
			case Lbls of
				[X] -> {SC,X};
				_ -> false
			end;
		false -> false
	end.

-spec(is_ball/2 :: (states(),lbl_transitions()) -> bool()).
is_ball(SC,Trans) ->			
	lists:all(fun(X) -> X end,
			  [ lists:member(S2,SC) || {S1,S2,_St} <- Trans,
									   lists:member(S1,SC)]).

-spec(collapse_balls/2 :: 
	  ([{states(),label()}],non_lbl_buchi()) -> non_lbl_buchi()).
collapse_balls([],B) -> B;
collapse_balls(SCs,{States,InitStates,Trans,Accept}) ->
	InTrans = lists:map(fun({SC,_}) ->
								[ {S1,St} || {S1,S2,St} <- Trans, 
											 lists:member(S2,SC),
											 not lists:member(S1,SC)]
						end,SCs),
	NewStates = lists:seq(length(States) + 1,length(States) + length(SCs)),
	NewTrans = lists:flatmap(fun({NS,{_SC,Lbl},InTrs}) ->
									 [{NS,NS,Lbl}] ++ [{S1,NS,St} || {S1,St} <- InTrs]
							 end,lists:zip3(NewStates,SCs,InTrans)),
	Rem = lists:flatten([SC || {SC,_} <- SCs]),
	B = remove(Rem,{States ++ NewStates,InitStates,Trans ++ NewTrans, Accept ++ NewStates}),
	%% 	io:format("NewState: ~p\nNewTrans: ~p\nRem: ~p\n ==> B: ~p\n",[NewStates,NewTrans,Rem,B]),
	B.


-type(color() :: integer()).
-type(color_set() :: [{state(),color()}]).
-spec(basic_bisim_red/1 :: (non_lbl_buchi()) -> non_lbl_buchi()).
basic_bisim_red(_B = {States,InitStates,Trans,Accept}) ->
	CInit0 = lists:reverse([{N,1} || N <- States]),
	CInit1 = lists:usort([{N,1} || N <- Accept] ++ [{N,2} || N <- States -- Accept]),
	Cs = bbr(CInit0,CInit1,States,Trans),
	NStates = lists:usort([ C || {_S,C} <- Cs]),
	NAccept = lists:usort([ lkp_c(S,Cs) || S <- Accept]),
	NInitStates = lists:usort([ lkp_c(S,Cs) || S <- InitStates]),
	NTrans = lists:usort([{lkp_c(S1,Cs),lkp_c(S2,Cs),St} || {S1,S2,St} <- Trans]),
	{NStates,NInitStates,NTrans,NAccept}.


-spec(bbr/4 ::
	  (color_set(),color_set(),states(),lbl_transitions()) -> color_set()).
bbr(C0,C1,Ss,Trs) ->
	%%  	io:format("C0: ~p \nC1: ~p\n",[C0,C1]),
	case C0 == C1 of
		true -> C1;
		false ->
			C2a = [ {lkp_c(S,C1),
					 [{lkp_c(S2,C1),St} || {X,S2,St} <- Trs,X == S]} 
					|| S <- Ss],
			%%  			io:format("C1: ~p\nC2a: ~p\n", [C1,C2a]),
			C2b = lists:usort(C2a),
			C2c = lists:zip(C2b,lists:seq(1,length(C2b))),

			Orig = lists:zip(Ss,C2a),
			C2 = [{S,proplists:get_value(C,C2c)} || {S,C} <- Orig],

			bbr(C1,C2,Ss,Trs)
	end.

-spec(lkp_c/2 :: (state(),color_set()) -> color()).
lkp_c(Elem,Lst) ->
	%% 	io:format("lkp_c(~p,~p)\n",[Elem,Lst]),
	{value,{_,X}} = lists:keysearch(Elem,1,Lst),
	X.

-type(part_ord() :: [{color(),color(),bool()}]).
-type(nb_pair() :: {color(),label()}).
-type(nb_pairs() :: [nb_pair()]).
-type(neighbor_set() :: {state(),nb_pairs()}).
-type(neighbor_sets() :: [neighbor_set()]).
-spec(strong_fair_sim_red/1 :: (non_lbl_buchi()) -> non_lbl_buchi()).
strong_fair_sim_red(B = {States,InitStates,Trans,Accept}) ->
	io:format("B: ~w\n",[B]),
	CInit0 = [{N,1} || N <- States],
	CInit1 = lists:usort([{N,1} || N <- Accept] ++ [{N,2} || N <- States -- Accept]),
	PoInit0 = [],
	PoInit1 = [{2,1,true},{1,1,true},{2,2,true},{1,2,false}],
	{Cs,Ns} = sfsr(CInit0,CInit1,PoInit0,PoInit1,States,Trans),
	io:format("Res: ~p :: ~p\n",[Cs,Ns]),
	NStates = lists:usort([ C || {_S,C} <- Cs]),
	NAccept = lists:usort([ lkp_c(S,Cs) || S <- Accept]),
	NInitStates = lists:usort([ lkp_c(S,Cs) || S <- InitStates]),
	NTrans = lists:usort([{lkp_c(S1,Cs),lkp_c(S2,Cs),St} 
						  || {S1,S2,St} <- Trans,
							 lists:member({lkp_c(S2,Cs),St},
										  proplists:get_value(S1,Ns))
								]),
	{NStates,NInitStates,NTrans,NAccept}.

-spec(sfsr/6 ::
	  (color_set(),color_set(),part_ord(),
	   part_ord(),states(),lbl_transitions()) -> color_set()).
sfsr([],_,_,_,_,_) ->
	{[],[]};
sfsr(C0,C1,Po0,Po1,Ss,Trs) ->
	io:format("{ C0: ~p\n  C1: ~p\n  Po0: ~p\n  Po1: ~p\n}\n",[C0,C1,Po0,Po1]),
	N1 = i_max_neighbor_sets(Ss,Trs,C1,Po1),
	case C0 == C1 andalso length(Po0) == length(Po1) of
		true -> {C1,N1};
		false ->
			C2a = [{lkp_c(S,C1),proplists:get_value(S,N1)} || S <- Ss],
			C2b = lists:usort(C2a),
			io:format("N1: ~p\nC2: ~p\n",[N1,C2b]),
			Po2a =
				[ case po(C2i_1,C1i_1,Po1) andalso 
					  i_dominates_set(N1i_1,N2i_1,Po1) of
					  true  -> {C2i,C1i,true};
					  false -> {C2i,C1i,false}
				  end || C1i = {C1i_1,N1i_1} <- C2b,
						 C2i = {C2i_1,N2i_1} <- C2b],
			C2c = lists:zip(C2b,lists:seq(1,length(C2b))),
			C2 = [{S,proplists:get_value(C,C2c)} || {S,C} <- lists:zip(Ss,C2a)],
			Po2 = lists:usort([{proplists:get_value(Ci1,C2c),
								proplists:get_value(Ci2,C2c),V} || {Ci1,Ci2,V} <- Po2a]),
			io:format("C2: ~p\nPo2: ~p\n",[C2c,Po2]),
			sfsr(C1,C2,Po1,Po2,Ss,Trs)
	end.

-spec(i_max_neighbor_sets/4 ::
	  (states(),lbl_transitions(),color_set(),part_ord()) -> neighbor_sets()).
i_max_neighbor_sets(States,Trans,C,Po) ->
	[i_max_neighbor_set(S,Trans,C,Po) || S <- States].

-spec(i_max_neighbor_set/4 ::
	  (state(),lbl_transitions(),color_set(),part_ord()) -> neighbor_set()).
i_max_neighbor_set(State,Trans,C,Po) ->
	Neighbors = [ {lkp_c(S2,C),Lbl} || {S1,S2,Lbl} <- Trans, State == S1],
	io:format("Max_nb_set: ~p\n",[State]),
	io:format("~p has neighbors (with types):\n  ~w\n",
			  [State, Neighbors]),
    AltSet = i_max_nb_set(Neighbors,[],Po),
	io:format("Altset: ~p\n",[{State,AltSet}]),
	{State,
	 lists:usort([ {lkp_c(S2,C),Lbl} 
				   || Tr = {S1,S2,Lbl} <- Trans, State == S1,
					  i_maximal(S1,{lkp_c(S2,C),Lbl},Trans -- [Tr],C,Po)])},
	{State,AltSet}.

i_max_nb_set([],Set,_) ->
	lists:usort(Set);
i_max_nb_set([NBi | NBs],Set,Po) ->
	case [NBn || NBn <- NBs, i_dominates(NBn,NBi,Po)] of
		[] ->
			Dominated = [NBn || NBn <- NBs, i_dominates(NBi,NBn,Po)],
			i_max_nb_set(NBs -- Dominated,[NBi | Set],Po);
		_ -> 
			i_max_nb_set(NBs,Set,Po)
	end.
		

%% i_maximal
-spec(i_maximal/5 :: 
	  (state(),nb_pair(),lbl_transitions(),color_set(),part_ord()) -> bool()).
i_maximal(Q,{CQ1,Tau},Trans,C,Po) ->
	io:format("For ~p, is ~p i-maximal? Considering ~w\n",
			  [Q,{CQ1,Tau},
			   [Tr || Tr = {S1,S2,Lbl} <- Trans, S1 == Q]]),
	IDom = [ i_dominates({lkp_c(S2,C),Lbl},{CQ1,Tau},Po)
			 || {S1,S2,Lbl} <- Trans,
				Q == S1],
	io:format("For ~p, is ~p i-maximal? ~p\n",
			  [Q,{CQ1,Tau},not lists:any(fun(X) -> X end,IDom)]),
	not lists:any(fun(X) -> X end,IDom).

-spec(i_dominates/3 ::
	  (nb_pair(),nb_pair(),part_ord()) -> bool()).
%% i_dominates({C1,[]},{C2,_},Po) ->
%% 		false; %%po(C2,C1,Po); %% or false!
%% i_dominates({C1,Sig},{C2,Tau},Po) ->
%% 	case po(C2,C1,Po) andalso (Sig -- Tau == []) of
%% 			true -> %io:format("~p i-dominates ~p\n",[{C1,Sig},{C2,Tau}]),
%% 							true;
%% 			false -> false
%% 	end.

i_dominates({C1,Sig},{C2,Tau},Po) ->
	case po(C2,C1,Po) of
		false -> io:format("  - ~p i-dom ~p == FALSE  (po(~p,~p) == FALSE)\n",[{C1,Sig},{C2,Tau},C2,C1]),
			false;
		true ->
			case Sig of
				[] -> io:format("  - ~p i-dom ~p == TRUE (Empty case)\n",[{C1,Sig},{C2,Tau}]),
					  true;
				_ -> 
					case Sig -- Tau of
						[] -> io:format("  - ~p i-dom ~p == TRUE\n",[{C1,Sig},{C2,Tau}]),
							  true;
						_X ->  io:format("  - ~p i-dom ~p == FALSE (~w -- ~w == ~w)\n",[{C1,Sig},{C2,Tau},Sig,Tau,_X]),
							   false
					end
			end
	end.


%% 			true -> %io:format("~p i-dominates ~p\n",[{C1,Sig},{C2,Tau}]),
%% 							true;
%% 			false -> false
%% 	end.

-spec(i_dominates_set/3 ::
	  (nb_pairs(),nb_pairs(),part_ord()) -> bool()).
i_dominates_set(Nq1,Nq2,Po) ->		
	Res = lists:all(
			fun(X) -> X end,
			[ lists:any(fun(X) -> X end,
						[ i_dominates({C_,Sigma},{C,Tau},Po)
						  || {C_,Sigma} <- Nq1])
			  || {C,Tau} <- Nq2]),
	io:format("~w i-set-dominates ~w ? ~p\n",[Nq1,Nq2,Res]),
	Res.

-spec(po/3 :: (color(),color(),part_ord()) -> bool()).
po(X1,X2,[{X1,X2,B} | _]) -> B;
po(X1,X2,[_ | Po]) ->
	po(X1,X2,Po).

%%
%% (Internal) helper functions
%%
is_sat([], _) -> true;
is_sat([ltrue| Lits], Props) -> is_sat(Lits, Props); %% ???
is_sat([{lnot, Prop}| Lits], Props) ->
    not lists:member(Prop, Props) andalso is_sat(Lits, Props);
is_sat([Prop| Lits], Props) ->
    lists:member(Prop, Props) andalso is_sat(Lits, Props).

make_unlabeled(B) ->
    case is_labeled(B) andalso not is_nonlabeled(B) of
      true ->
	  io:format("*WARNING*: Changed buchi automata from labeled into non-labeled!!\n"),
	  lbl2nonlbl(B);
      false ->
	  B
    end.

%% labeled to non-labeled translation
lbl2nonlbl({[],_InitStates,_Trans,_Accepts}) ->
    {[1],[1],[],[]};
lbl2nonlbl(B = {States,InitStates,Trans,Accepts}) ->
    case is_labeled(B) of
		true -> 
			NewStates = [1 | [ S+1 || {S,_} <- States]],
			NewTrans = [{S1+1,S2+1,element(2,lists:nth(S2,States))} || {S1,S2} <- Trans] ++
				[{1,S+1,element(2,lists:nth(S,States))} || S <- InitStates],
			NewAccepts = case is_generalized(B) of
							 true -> [ [ S+1 || S <- SS] || SS <- Accepts];
							 false -> [ S+1 || S <- Accepts ]
						 end,
			{NewStates,[1],lists:usort(NewTrans),NewAccepts};
		false ->
			B
    end.

												% non-labeled to labeled translation
%% Doesn't make sense really...
%% nonlbl2lbl(B = {_States,_InitStates,Trans,Accepts}) ->
%%     case is_nonlabeled(B) of
%% 	true -> 
%% 	    NewInitStates = [S-1 || {1,S,_} <- Trans ],
%% 	    NewStates = lists:usort([{S-1,St} || {_,S,St} <- Trans ]),
%% 	    NewTrans = [{S1-1,S2-1} || {S1,S2,_} <- Trans, S1 > 1],
%% 	    NewAccepts = case is_generalized(B) of
%% 			     true -> [ [ S-1 || S <- SS, S > 1] || SS <- Accepts];
%% 			     false -> [ S-1 || S <- Accepts, S > 1 ]
%% 			 end,
%% 	    {NewStates,NewInitStates,lists:usort(NewTrans),NewAccepts};
%% 	false -> 
%% 	    B
%%     end.	

%% generalized_buchi() -> buchi()
degeneralize(B) ->
    degeneralize2(make_unlabeled(B)).
degeneralize2(B = {States,InitStates,Trans,Accepts}) ->
    case is_generalized(B) of
		false -> B;
		true ->
			case length(Accepts) of
				1 -> {States,InitStates,Trans,hd(Accepts)};
				_ ->	 
					Accepts1 = remove_subsets(Accepts),
					%% 		io:format("Accpts: ~p\nAccepts1: ~p\n",[Accepts,Accepts1]),
					Trans1 = degen_trans(Trans,length(States),length(Accepts1),Accepts1),
					Reachable = lists:usort(reachable(Trans1,InitStates)),
					Trans2 = [{S1,S2,St} || {S1,S2,St} <- Trans1, lists:member(S1,Reachable)],
					Accept = [S || S <- hd(Accepts1),lists:member(S,Reachable)],
					StMap = lists:zip(lists:seq(1,length(Reachable)),Reachable),
					Trans3 = lists:map(
							   fun({S1,S2,St}) -> 
									   {stmap(S1,StMap),stmap(S2,StMap),St} 
							   end,Trans2),
					States1 = [ New || {New,_Old} <- StMap],
					InitStates1 = lists:map(fun(S) -> stmap(S,StMap) end,InitStates),
					Accept1 = lists:map(fun(S) -> stmap(S,StMap) end,Accept),
					{States1,InitStates1,Trans3,Accept1}
			end
	end.

stmap(N, Ns) ->
    case lists:keysearch(N, 2, Ns) of {value, {N2, N}} -> N2 end.

                                                  %% 	_ -> io:format("Error ~p not in ~p\n",[N,Ns]),
						  %% 	     1 = 2


offset(S,Ns) ->
    case S rem Ns of
		0 -> Ns;
		X -> X
    end.

degen_trans(Trans, NStates, NCopies, Accepts) ->
    %% 'Loops' can be combined, lists:member can only match some transitions...
    Trans1 = [{N * NStates + S1, N * NStates + S2, St}
	      || {S1, S2, St} <- Trans,
		 N <- lists:seq(0, NCopies - 1)],
    %% 	io:format("Trans1: ~p\n",[Trans1]),
    lists:foldl(fun ({N, F}, Ts) ->
			F2 = lists:map(fun (X) -> X + NStates * N end, F),
			%% 					 io:format("F2: ~p\n",[F2]),
			lists:map(fun ({S1, S2, St}) ->
					  case lists:member(S1, F2) of
					    true ->
						{S1, offset(S2, NStates) + NStates * ((N + 1) rem NCopies), St};
					    false ->
						{S1, S2, St}
					  end
				  end, Ts)
		end, Trans1, lists:zip(lists:seq(0, NCopies - 1), Accepts)).

remove_subsets(Lists) ->
	lists:map(fun sets:to_list/1,
			  remove_subsets1(lists:map(fun sets:from_list/1,Lists),[])).

remove_subsets1([],Sets) ->
	Sets;
remove_subsets1([Set | Sets],Sets2) ->
	case sets:to_list(Set) == [] of
		true -> remove_subsets1(Sets,[Set | Sets2]);
		false ->
			case not lists:any(fun(X) -> X end,
							   lists:map(fun(X) -> sets:is_subset(Set,X) end,Sets ++ Sets2)) of
				true  -> remove_subsets1(Sets,[Set | Sets2]);
				false -> remove_subsets1(Sets,Sets2)
			end
	end.





%% A dfs...
reachable(Trans,InitStates) ->
    reachable(Trans,InitStates,[]).

reachable(_,[],Reached) ->	
    Reached;
reachable(Trans,[State|States],Reached) ->
    {States2,Reached2} = reachable(State,Trans,States,Reached),
    reachable(Trans,States2,Reached2).

reachable(State, [], States, Reached) ->
    {States, [State| Reached]};
reachable(State, [{S1, S2, _}| Trans], States, Reached) ->
    case S1 == State andalso not lists:member(S2, [State| States]) andalso
			       not lists:member(S2, Reached)
	of
      true ->
	  reachable(State, Trans, [S2| States], Reached);
      false ->
	  reachable(State, Trans, States, Reached)
    end;
reachable(State, [{S1, S2}| Trans], States, Reached) ->
    case S1 == State andalso not lists:member(S2, [State| States]) andalso
			       not lists:member(S2, Reached)
	of
      true ->
	  reachable(State, Trans, [S2| States], Reached);
      false ->
	  reachable(State, Trans, States, Reached)
    end.

%% Build buichi-digraph
buchi2digraph(B = {States, _InitStates, Trans, Accept}) ->
    case is_nonlabeled(B) andalso not is_generalized(B) of
      false ->
	  io:format("ERR_B: ~p\n", [B]),
	  io:format("*ERROR*: Can only build digraph from non-labeled and " ++
		      "non-generalized buchi automaton!\n"),
	  {error, bad_automata};
      true ->
	  G = digraph:new([cyclic]),
	  lists:foreach(fun (N) ->
				digraph:add_vertex(G, N, lists:member(N, Accept))
			end, States),
	  lists:foreach(fun ({S1, S2, St}) ->
				digraph:add_edge(G, S1, S2, St)
			end, Trans),
	  {ok, G}
    end.

removable([],_Trans) ->	
    [];
removable([S = {_S,[]} | States], Trans) ->
    [S | removable(States,Trans)];
removable([S = {Si,_St} | States], Trans) ->
    case lists:filter(fun({X,_Y}) -> X == Si end,Trans) of
		[] -> [S | removable(States,Trans)];
		_ -> removable(States,Trans)
    end.

remove(RStates,B) ->
    case is_labeled(B) of
		true ->  remove_lbl(RStates,B);
		false -> remove_nonlbl(RStates,B)
    end.

remove_lbl(RStates,B = {States,InitStates,Trans,Accepts}) ->
    NewStates = States -- RStates,
    RStates2 = [S || {S,_} <- RStates],
    case NewStates of
		[] -> {[],[],[],[]};
		_ ->
			StMap = lists:zip(lists:seq(1,length(NewStates)),
							  [ S || {S,_} <- NewStates]),
			NewInitStates = [ stmap(S,StMap) || S <- InitStates,
												not lists:member(S,RStates2) ],
			NewTrans = [ {stmap(S1,StMap),stmap(S2,StMap)} 
						 || {S1,S2} <- Trans, 
							not lists:member(S1,RStates2),
							not lists:member(S2,RStates2)],
			NewAccept = case is_generalized(B) of
							true ->
								[ [ stmap(S,StMap) || 
									  S <- SS, not lists:member(S,RStates2) ] || SS <- Accepts ];
							false ->
								[ stmap(S,StMap) || S <- Accepts, not lists:member(S,RStates2) ]
						end,
			{lists:zip(lists:seq(1,length(NewStates)),[St || {_,St} <- NewStates]),
			 NewInitStates,NewTrans,NewAccept}
    end.						

remove_nonlbl(RStates,B = {States,InitStates,Trans,Accepts}) ->
    NewStates = States -- RStates,
    case NewStates of
		[] -> {[],[],[],[]};
		_ ->
			StMap = lists:zip(lists:seq(1,length(NewStates)),NewStates),
			NewInitStates = [ stmap(S,StMap) || S <- InitStates,
												not lists:member(S,RStates) ],
			NewTrans = [ {stmap(S1,StMap),stmap(S2,StMap),St} 
						 || {S1,S2,St} <- Trans, 
							not lists:member(S1,RStates),
							not lists:member(S2,RStates)],
			NewAccept = case is_generalized(B) of
							true ->
								[ [ stmap(S,StMap) || 
									  S <- SS, not lists:member(S,RStates) ] || SS <- Accepts ];
							false ->
								[ stmap(S,StMap) || S <- Accepts, not lists:member(S,RStates) ]
						end,
			{lists:seq(1,length(NewStates)),
			 NewInitStates,NewTrans,NewAccept}
    end.						

%%%%% Unstructured stuff below

btest() ->
    {[{1,[]},{2,[b]},{3,[b]},{4,[]}],
     [1],
     [{1,1},{1,2},{1,3},{2,4},{3,4},{4,4}],
     [[2,4],[3,4]]}.

btest1() ->
    {[1,2],
     [1],
     [{1,1,[a]},{1,2,[b]},{2,2,[b]},{2,1,[a]}],
     [1]}.

btest2() ->
    {[1,2],
     [1],
     [{1,1,[a]},{1,2,[b]},{2,2,[b]},{2,1,[a]}],
     [2]}.

btest3() ->
	{[1,2,3],
	 [1],
	 [{1,2,[]},{2,3,[a]},{3,2,[a]}],
	 [2,3]}.


sfsr_test2() ->
	{[1,2,3,4,5],
	 [1],
	 [{1,2,[{lprop,p1}]},{2,2,[]},{1,3,[{lprop,p1},{lprop,p2}]},
	  {3,4,[{lprop,p2}]},{4,5,[{lprop,p2}]},{5,4,[]}],
	 [2,4]}.

sfsr_test() ->
	{[1,2,3,4],
	 [1],
	 [{1,2,[{lprop,p1}]},{2,2,[]},{1,3,[{lprop,p1},{lprop,p2}]},
	  {3,4,[{lprop,p2}]},{4,4,[]}],
	 [2]}.

sfsr_fail1() ->
	{[1,2,3],
	 [1],
	 [{1,2,[]},{2,3,[{lprop,x}]},{3,3,[{lprop,x}]},{3,2,[]}],
	 [2]}.

sfsr_fail2() ->
	{[1,2,3],[1],[{1,2,[]},{2,2,[]},{2,3,[]}],[2,3]}. 

sfsr_fail3() ->
	{[1,2,3],
     [3],
     [{1,1,[]},
      {2,1,[{lprop,x}]},
      {2,2,[]},
      {3,1,[{lprop,x}]},
      {3,2,[{lprop,x}]}],
     [1,2]}.

sfsr_fail4() ->
	{[1,2,3],
     [3],
     [{1,1,[]},
      {2,2,[]},
      {3,1,[{lprop,x}]},
      {3,2,[{lprop,x}]}],
     [1,2]}.
