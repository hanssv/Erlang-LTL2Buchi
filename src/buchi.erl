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

%% @author Hans Svensson <hanssv@chalmers.se>
%% @copyright 2009, Hans Svensson
%% @doc Module defining Buchi automata + utility functions
%%
%% @type buchi_automaton(). A tuple structure representing a Buchi automaton.
%% @todo Use digraphs for representing Buchi automata.

-module(buchi).

-export([is_labeled/1,is_nonlabeled/1,is_generalized/1,size_of/1,
		 is_empty/1,intersection/2,
		 reachable_loop_states/1, ltl_intersection/2, reachable/1,
		 lbl2nonlbl/1, 
		 buchi2digraph/1,remove_subsets/1,
		 empty_buchi/0,empty_labeled_buchi/0,
		 degeneralize/1, sccs/1]).

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

%-type(gen_buchi() :: gen_lbl_buchi() | gen_non_lbl_buchi()).
%-type(non_gen_buchi() :: lbl_buchi() | non_lbl_buchi()).

-type(labeled_buchi() :: gen_lbl_buchi() | lbl_buchi()).
-type(non_labeled_buchi() :: gen_non_lbl_buchi() | non_lbl_buchi()).

-type(buchi() :: labeled_buchi() | non_labeled_buchi()).

%%
%% Buchi recognizers
%%
%% True if the BA has its labels in the states
-spec(is_labeled/1::(buchi())->bool()).
%% @doc Recognize labelled Buchi automaton.
%% @spec (buchi_automaton()) -> bool()
is_labeled({_,_,[{_,_} | _],_}) ->
    true;
is_labeled({[{_,_} | _],_,_,_}) ->
    true;
is_labeled({[],_,[],_}) ->
    true;
is_labeled(_) ->
    false.

-spec(is_nonlabeled/1::(buchi())->bool()).
%% @doc Recognize non-labeled Buchi automaton.
%% @spec (buchi_automaton()) -> bool()
is_nonlabeled({_,_,[{_,_,_} | _],_}) ->
    true;
is_nonlabeled({[X|_],_,[],_}) when is_integer(X) ->
    true;
is_nonlabeled({[],_,[],_}) ->
    true;
is_nonlabeled(_) ->
    false.

%% True if The BA is generalized
-spec(is_generalized/1::(buchi())->bool()).
%% @doc Recognize generalized Buchi automaton.
%% @spec (buchi_automaton()) -> bool()
is_generalized({_,_,_,[Ac | _]}) ->
    is_list(Ac);
is_generalized(_) ->
    false.

-spec(size_of/1::(buchi())->integer()).
%% @doc Size of Buchi automaton.
%% Returns a (bad) measure of the size of the BA
%% @spec (buchi_automaton()) -> int()
size_of({States,_InitStates,Trans,_Accepts}) ->
    length(States) + length(Trans).


%%
%% Main functions on BA
%%

%% The empty BA
-spec(empty_buchi/0::()->(non_labeled_buchi())).
%% @doc The empty non-labeled Buchi automaton.
%% @spec () -> buchi_automaton()
empty_buchi() -> {[1],[1],[],[]}.

-spec(empty_labeled_buchi/0::()->(labeled_buchi())).
%% @doc The empty labeled Buchi automaton.
%% @spec () -> buchi_automaton()
empty_labeled_buchi() -> {[],[],[],[]}.

%% Empty check
-spec(is_empty/1::(buchi())->bool()).
%% @doc Check Buchi automaton for emptiness.
%% @spec (buchi_automaton()) -> bool()
is_empty(B = {_States,_InitStates,_Trans,_Accept}) ->
    case reachable_loop_states(B) of
		[] -> true;
		_ -> false
    end.

-spec(reachable_loop_states/1::(non_lbl_buchi())->states()).
%% @private
reachable_loop_states(B = {_States,InitStates,_Trans,Accept}) ->
    {ok,G} = buchi2digraph(B),
    Reachable = digraph_utils:reachable(InitStates,G),
    Res = [ V || V <- Accept,
				 lists:member(V,Reachable),
				 digraph:get_cycle(G,V) /= false],
	digraph:delete(G),
	Res.


-spec(intersection/2::(buchi(),buchi())->non_lbl_buchi()).
%% @doc Intersection of two Buchi automata.
%% Computes the product/intersection of two BA's,
%% the result is a non-generalized, non-labeled BA.
%% @spec (buchi_automaton(),buchi_automaton()) -> buchi_automaton()
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

%% @doc LTL intersection of Buchi automaton and LTL 
%% formula translated to Buchi automaton. 
%% The first BA is a System model (or an automata generated
%% from a witness) and the second BA is generated from an 
%% LTL formula. Maybe this operation has a better name!??
%% @spec (buchi_automaton(),buchi_automaton()) -> buchi_automaton()
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

%% @doc Translate labeled Buchi automaton into non-labeled.
%% @spec (buchi_automaton()) -> buchi_automaton()
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

%% non-labeled to labeled translation
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
%% @doc Translate generalized Buchi automaton into non-generalized.
%% @spec (buchi_automaton()) -> buchi_automaton()
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

%% @private
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
%% @doc Return all reachable states of Buchi automaton.
%% Does a depth first traversal of the automaton.
%% @spec (buchi_automaton()) -> [state()]
reachable(_B = {_States,InitStates,Trans,_Accept}) ->
	reachable(Trans,InitStates).

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
%% @doc Translate  Buchi automaton into digraph.
%% @see //stdlib/digraph. digraph
%% @spec (buchi_automaton()) -> digraph()
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

%% @private
sccs(B) ->
	{ok,G} = buchi2digraph(B),
	io:format("SCCS: ~p\n",[digraph_utils:strong_components(G)]),
	digraph:delete(G).
