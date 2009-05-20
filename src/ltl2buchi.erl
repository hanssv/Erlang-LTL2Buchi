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

%%% File    : ltl2buchi.erl
%%% Author  : Hans Svensson <>
%%% Description : LTL to Büchi translation in the spirit of LTL2BUCHI
%%%               (Java - NASA - Giannakopoulou & Lerda)
%%% Created :  5 Mar 2009 by Hans Svensson <>

-module(ltl2buchi).

-export([convert/1,translate/1,translate_norew/1]).
-export([simplify/1]).
-export([permutations/1,selections/1]).

-record(node,{nodeid,
			  incoming = [],
			  tobedone = [], origphi = undefined,
			  old = [], next = [], 
			  eventualites = [], 
			  accepting = undefined, 
			  root_collapsed = false,
			  equivclass = undefined}).

-define(DEBUG,0).

convert(Phi) ->
%% 	B = translate(fix_ltl_format(Phi)),
 	_B = translate(Phi).
%% 	buchi_to_mcerlang_digraph(B).

translate(Phi) ->
	RPhi = ltl_rewrite:rewrite(Phi),
	Bs = ltl2buchi(RPhi),
	OptBs = lists:map(fun buchi_reduce:reduce/1,Bs),
	_OptB = pick_smallest(OptBs).

translate_norew(Phi) ->
	Bs = ltl2buchi(Phi),
	OptBs = lists:map(fun buchi_reduce:reduce/1,Bs),
	_OptB = pick_smallest(OptBs).

%%% Pick the best!
pick_smallest(Bs) ->
	hd(lists:sort(fun(B1,B2) ->
						  buchi_reduce:size_of(B1) < buchi_reduce:size_of(B2)
				  end,Bs)).


%%%
%% Convert tuple-based Buchi automata to digraph 
%% variant defined in buchi.erl
%%% 
%% buchi_to_mcerlang_digraph({States,InitStates,Trans,Accept}) ->
%% 	G = buchi:new(),
%% 	lists:foreach(
%% 	  fun(S) ->
%% 			  buchi:add_state(S-1,
%% 							  [initial   || lists:member(S,InitStates)] ++
%% 							  [accepting || lists:member(S,Accept)],
%% 							  G)
%% 	  end,States),
%% 	lists:foreach(
%% 	  fun({S1,S2,Lbl}) ->
%% 			  buchi:add_transition(S1-1,
%% 								   convert_label(Lbl),
%% 								   S2-1,
%% 								   G)
%% 	  end,Trans),
%% 	G.

%% convert_label([]) ->
%% 	buchi:boolean_condition(true);
%% convert_label([X]) ->
%% 	convert_literal(X);
%% convert_label([X | Xs]) ->
%% 	buchi:and_condition(convert_literal(X),convert_label(Xs)).

%% convert_literal({lnot,P}) ->
%% 	buchi:neg_condition(convert_literal(P));
%% convert_literal(ltrue) ->
%% 	buchi:pred_condition(true);
%% convert_literal(lfalse) ->
%% 	buchi:pred_condition(false);
%% convert_literal({lprop,X}) ->
%% 	buchi:pred_condition(X).

%%%
%% Core translation
%%%

%% Remove always, eventually
simplify({always,Phi}) ->
	simplify({release,lfalse,Phi});
simplify({eventually,Phi}) ->
	simplify({until,ltrue,Phi});
simplify({Op,Phi}) -> 
	{Op,simplify(Phi)};
simplify({Op,Phi1,Phi2}) ->
	{Op,simplify(Phi1),simplify(Phi2)};
simplify(Phi) -> 
	Phi.

%% Boolean simplification
bool_simp({land,Phi1,Phi2}) ->
	case {bool_simp(Phi1),bool_simp(Phi2)} of
		{ltrue,X} -> X;
		{lfalse,_} -> lfalse;
		{X,ltrue} -> X;
		{_X,lfalse} -> lfalse;
		{X,Y} -> {land,X,Y}
	end;
bool_simp({lor,Phi1,Phi2}) ->
	case {bool_simp(Phi1),bool_simp(Phi2)} of
		{ltrue,_} -> ltrue;
		{lfalse,X} -> X;
		{_,ltrue} -> ltrue;
		{X,lfalse} -> X;
		{X,Y} -> {lor,X,Y}
	end;
bool_simp({lnot,ltrue}) -> lfalse;
bool_simp({lnot,lfalse}) -> ltrue;
bool_simp({Op,Phi}) -> 
	{Op,bool_simp(Phi)};
bool_simp({Op,Phi1,Phi2}) ->          
	{Op,bool_simp(Phi1),bool_simp(Phi2)};
bool_simp(Phi) ->                     
	Phi.

decompose_ands({land,Phi1,Phi2}) ->
	decompose_ands(Phi1) ++ decompose_ands(Phi2);
decompose_ands(Phi) ->
	[Phi].

ltl2buchi(Phi) ->
 	SPhi = ltl:pnf(simplify(Phi)),
 	prt_debug(1,"Formula: ~s\n",[ltl:pp(SPhi,java)]),
	Init = #node{nodeid = 0,
				 equivclass = 0,
				 origphi = SPhi,
				 next = decompose_ands(SPhi)},
	NodeSet = expand(Init,[]),
 	prt_debug(4,"~p\n",[NodeSet]),
	case NodeSet of
		[] -> [{[],[],[],[]}];
		_ ->
			EqClasses = lists:usort([Eq || #node{equivclass = Eq} <- NodeSet]),
			States = lists:seq(1,length(EqClasses)),
			EqMap = lists:zip(EqClasses,States),
			StMap = [{St,Eq} || #node{nodeid = St, equivclass = Eq} <- NodeSet],
			NodeSet2 = optimize_acc_sets(NodeSet,SPhi),
			InitStates = [proplists:get_value(proplists:get_value(0,StMap),EqMap)],
			TransAc = %%lists:usort(
						[ {proplists:get_value(proplists:get_value(N2,StMap),EqMap),
						   proplists:get_value(proplists:get_value(N1,StMap),EqMap),
						   Old,Acc}
						  || #node{nodeid = N1,old = Old, 
								   incoming = Ins, accepting = Acc} <- NodeSet2,
							 N2 <- Ins],%),
			TransAc_ = [{1,1,[],[2]},
					   {1,1,[{lprop,a}],[1,2]},
					   {1,1,[{lprop,a}],[1,2]},
					   {1,2,[],[1]},
					   {2,1,[{lprop,a}],[1,2]},
					   {2,2,[],[1]}],
  			prt_debug(1,"Generalized buchi automata: ~p states ~p transitions\n",
  					  [length(States), length(TransAc)]),
 			prt_debug(2,"Gen: ~p\n",[{States,InitStates,TransAc}]),
			_Bs = degeneralize_tgba(States,InitStates,TransAc)
	end.

expand(Node,NodeSet) ->
 	prt_debug(4,"Xpand entered!\n"),
	case Node#node.tobedone of
		[] ->
 			prt_debug(4,"Tobedone is empty\n"),
			Node1 = compute_accepting(Node),
			case find_equivalent(Node1,NodeSet) of
				none ->
 					prt_debug(5,"No match found for ~p\n",[Node#node.nodeid]),
					Node2 = Node1#node{equivclass = make_ref()},
					NewNode = #node{nodeid = make_ref(),
									origphi = Node#node.origphi,
									incoming = [Node#node.nodeid],
									tobedone = Node#node.next},
 					prt_debug(4,"Creating: ~p (TBD: ~p)\n",[NewNode#node.nodeid,
 														  [ltl:pp(L,java) || L <- NewNode#node.tobedone]]),
 					prt_debug(5,"1 new node in set\n"),
					expand(NewNode,[Node2 | NodeSet]);
				EqNode ->
 					prt_debug(5,"Match found ~p\n",[EqNode#node.nodeid]),
 					prt_debug(4,"Node ~p, collapsed with ~p\n",[Node#node.nodeid,EqNode#node.nodeid]),
					merge(EqNode,Node1,(NodeSet -- [EqNode]))
			end;
		[NextFormula | NewToBeDone] ->
 			prt_debug(4,"Expanding: ~p for node ~p\n",[ltl:pp(NextFormula,java),Node#node.nodeid]),
			case contradicts(NextFormula,Node) of
				true ->
 					prt_debug(4,"Contradicting formula, skipping ~p\n",[Node#node.nodeid]),
					NodeSet;
				false ->
					Node1 = update_fulfilled_obligations(
							  Node#node{tobedone = NewToBeDone}, NextFormula),
					case is_redundant(NextFormula, Node) of
						true ->
 							prt_debug(4,"Formula ~p redundant\n",[NextFormula]),
							expand(Node1,NodeSet);
						false ->
							Node2 = update_promised_obligations(Node1,NextFormula),
							expand_next_formula(NextFormula,Node2,NodeSet)
					end
			end
	end.


%% TODO: Fix the is_redundant thing for next, generalize and add and-decomposition!
expand_next_formula(NextFormula,Node,NodeSet) ->
	case NextFormula of
		{until,Psi,Phi} ->
			Node2 = Node#node{nodeid = make_ref(),
							  tobedone = set_add(Node#node.tobedone, 
												 ([Phi] -- Node#node.old))},
 			prt_debug(4,"Creating: ~p (TBD: ~p)\n",[Node2#node.nodeid,[ltl:pp(L,java) || L <- Node2#node.tobedone]]),
			Node1 = Node#node{tobedone = set_add(Node#node.tobedone,
												 ([Psi] -- Node#node.old)),
							  next = case is_redundant(NextFormula,Node#node.next,[]) of
										 true -> Node#node.next;
										 false -> set_add(Node#node.next,[NextFormula])
									 end},
			expand(Node2,expand(Node1,NodeSet));
		{release,Psi,Phi} ->
			Node2 = Node#node{nodeid = make_ref(),
							  tobedone = set_add(Node#node.tobedone,
												 ([Psi,Phi] -- Node#node.old))},
 			prt_debug(4,"Creating: ~p (TBD: ~p)\n",[Node2#node.nodeid,[ltl:pp(L,java) || L <- Node2#node.tobedone]]),
			Node1 = Node#node{tobedone = set_add(Node#node.tobedone,
												 ([Phi] -- Node#node.old)),
							  next = case is_redundant(NextFormula,Node#node.next,[]) of
										 true -> Node#node.next;
										 false -> set_add(Node#node.next,[NextFormula])
									 end},
			expand(Node2,expand(Node1,NodeSet));
		{lor,Phi1,Phi2} ->
			Node2 = Node#node{nodeid = make_ref(),
							  tobedone = set_add(Node#node.tobedone,
												 ([Phi2] -- Node#node.old))},
 			prt_debug(4,"Creating: ~p (TBD: ~p)\n",[Node2#node.nodeid,[ltl:pp(L,java) || L <- Node2#node.tobedone]]),
			Node1 = Node#node{tobedone = set_add(Node#node.tobedone,
												 ([Phi1] -- Node#node.old))},
			expand(Node2,expand(Node1,NodeSet));
		{land,Phi1,Phi2} ->
			Node1 = Node#node{tobedone = set_add(Node#node.tobedone,
												 ([Phi1,Phi2] -- Node#node.old))},
			expand(Node1,NodeSet);
		{next,Phi} ->
			Node1 = Node#node{next = set_add(Node#node.next,[Phi])},
			expand(Node1,NodeSet);
		Lit ->
 			prt_debug(4,"Added to ~p literal ~p\n",[Node#node.nodeid,ltl:pp(Lit,java)]),
			Node1 = Node#node{old = set_add(Node#node.old,[bool_simp(Lit)])},
			expand(Node1,NodeSet)
	end.				


in_synt_impl(ltrue,_A,_B) ->
	true;
in_synt_impl(Mu,A,B) ->
	case lists:member(Mu,A) of
		true  -> true;
		false ->
			case Mu of
				{until,Psi,Phi} ->
					(lists:member(Mu,B) andalso in_synt_impl(Psi,A,B)) orelse
						in_synt_impl(Phi,A,B);
				{release,Psi,Phi} ->
					(lists:member(Mu,B) andalso in_synt_impl(Phi,A,B)) orelse
					(in_synt_impl(Psi,A,B) andalso in_synt_impl(Phi,A,B));
				{lor,Phi1,Phi2} ->
					in_synt_impl(Phi1,A,B) orelse in_synt_impl(Phi2,A,B);
				{land,Phi1,Phi2} ->
					in_synt_impl(Phi1,A,B) andalso in_synt_impl(Phi2,A,B);
				{next,Phi} ->
					lists:member(Phi,B);
				_ ->
					false
			end
	end.

contradicts(Phi,#node{old = Old, next = Next}) ->
	in_synt_impl(ltl:pnf(ltl:negate(Phi)),Old,Next).

is_redundant(Phi,#node{old = Old, next = Next}) ->
	is_redundant(Phi,Old,Next).
is_redundant(Phi,Old,Next) ->
	case lists:member({release,lfalse,Phi},Old) of
		true -> true;
		false ->
			in_synt_impl(Phi,Old,Next) andalso
				case Phi of
					{until,_,Psi} -> in_synt_impl(Psi,Old,Next);
					_ -> true
				end
	end.

find_equivalent(_Node,[]) ->
	none;
find_equivalent(#node{next = Next},[N = #node{next = Next} | _]) ->
	N;
find_equivalent(Node,[_|Nodes]) ->
	find_equivalent(Node,Nodes).

merge(N1 = #node{old = Old1, accepting = Acc1}, 
	  N2 = #node{old = Old2, accepting = Acc2}, NodeSet) ->
	case (Old1 == Old2 andalso Acc1 == Acc2) of
		true ->
			[N1#node{incoming = set_add(N1#node.incoming,N2#node.incoming)} | NodeSet];
		false ->
			case (Old1 == Old2 andalso N1#node.nodeid == 0 andalso N1#node.root_collapsed == false) of
				true ->
					[N1#node{incoming = set_add(N1#node.incoming,N2#node.incoming),
							 root_collapsed = true,
							 accepting = Acc2} | NodeSet];
				false ->
 					prt_debug(5,"1 new node in set\n"),
					[N1 | [N2#node{equivclass = N1#node.equivclass} | NodeSet]]
			end
	end.

update_fulfilled_obligations(N = #node{origphi = Phi, eventualites = Evs},Form) ->
	Untils = get_untils(Phi),
	UntilRHS = lists:map(fun({_,_,X}) -> X end,Untils),
	case lists:member(Form,UntilRHS) of
		true -> N#node{eventualites = set_add(Evs,[Form])};
		false -> N
	end.

update_promised_obligations(N = #node{eventualites = Evs}, F = {until,_,_}) ->
	N#node{eventualites = set_add(Evs,[F])};
update_promised_obligations(N, _) ->
	N.

compute_accepting(N = #node{origphi = Phi, eventualites = Evs}) ->
	Untils = get_untils(Phi),
	Accept = [ UPhi || UPhi = {_,_,RHPhi} <- Untils,
					   (not lists:member(UPhi,Evs)) orelse lists:member(RHPhi,Evs)],
	N#node{accepting = Accept}.

set_add(S1,S2) ->
	lists:usort(S1 ++ S2).

get_untils(F) ->
	lists:usort(get_untils2(F)).
get_untils2(F = {until,Psi,Phi}) ->
	[F | get_untils2(Psi) ++ get_untils2(Phi)];
get_untils2({_,Phi1,Phi2}) ->
	get_untils2(Phi1) ++ get_untils2(Phi2);
get_untils2({_,Phi}) ->
	get_untils2(Phi);
get_untils2(_) ->
	[].

%% Remove accepting sets that are supersets of other accepting sets
%% Needs a bit of massageing... Changes Formulas to numbers in accepting
optimize_acc_sets(NodeSet,SPhi) ->
	AcMap = case get_untils(SPhi) of
				[] -> [];
				Untils  ->lists:zip(Untils,lists:seq(1,length(Untils)))
			end,
	case AcMap of
		[] -> [N#node{accepting = [1]} ||	N <- NodeSet]; %% No AcMap ==> all accepting
		_  ->
			NodeSet2 = [N#node{accepting = [proplists:get_value(U,AcMap) || U <- Acc]}
						||	N = #node{accepting = Acc} <- NodeSet],
			AccSets1 = [{Id,A} || #node{nodeid = Id, accepting = Acc} <- NodeSet2, 
								  A <- Acc],
			AccSets2 = [{N,[Id || {Id,N2} <- AccSets1, N == N2]} 
						|| N <- safe_seq(1,length(AcMap))],
			ToRemove = [ N2 || {N1,Set1} <- AccSets2,
							   {N2,Set2} <- AccSets2,
							   N1 /= N2,
							   Set1 -- Set2 == [],
							   (Set1 /= Set2 orelse N1 > N2)],
			Acs = lists:map(fun({_,X}) -> X end,AcMap),
			NewAcMap = lists:zip(Acs -- ToRemove, safe_seq(1,length(Acs -- ToRemove))),
			prt_debug(5,"opt: ~p\n",[{AcMap,ToRemove,NewAcMap}]),
			NS = [N#node{accepting = lists:sort([proplists:get_value(A,NewAcMap) 
												 || A <- Acc -- ToRemove])} 
				  || N = #node{accepting = Acc} <- NodeSet2],
			prt_debug(5,"NS: ~p\n",[NS]),
			NS
	end.



degeneralize_tgba(_States,_InitState,[]) ->
	[{[],[],[],[]}];
degeneralize_tgba(States,InitState,Trans) ->
	NbrAccSets = length(lists:usort([ A || {_,_,_,As} <- Trans, A <- As])),
%%  	{DS2,DTrs2,DAc2} = build_degen(NbrAccSets),
%%   	{DS,DTrs,DAc} = {[0,1,2],[{0,0,[0,1]},{0,1,[]},{0,2,[0]},
%%   							  {1,0,[0,1]},{1,1,[]},{1,2,[0]},
%%   							  {2,2,[]},{2,0,[1]}],[0]},
%% 	{SS,TS,IS} = {[0,1,2],[{0,0,[],[1]},{0,1,[a],[0,1]},{0,2,[],[0]},{0,2,[a],[0,1]},
%% 						   {1,1,[],[0,1]},
%% 						   {2,2,[],[0]},{2,2,[a],[0,1]}],[0]},
%%  	prt_debug("Degen automata:\n   ~p\n",[{DS,[0],DTrs,DAc}]),
%%  	prt_debug("Bs: ~p\n",[synch_product({DS,[0],DTrs,DAc},{SS,IS,TS})]),

%%  	prt_debug("Degen automata:\n   ~p\n",[permute_ac([0,1],[1,0],{DS,[0],DTrs,DAc})]),
%%  	prt_debug("Bs: ~p\n",[synch_product(permute_ac([0,1],[1,0],{DS,[0],DTrs,DAc}),{SS,IS,TS})]),


%%  	prt_debug("Auto Degen automata:\n   ~p\n",[{DS2,DTrs2,DAc2}]),

	Gens =
		case NbrAccSets < 2 of
			true ->
				[{States,InitState,Trans}];
			false ->
				[ permute_ac_gen(lists:seq(1,NbrAccSets),P,{States,InitState,Trans})
				  || P <- permutations(lists:seq(1,NbrAccSets))]
		end,

	Degs = 
		case NbrAccSets of
			0 -> [{[],[],[],[]}];
			_ -> {DS_,DTrs_,DAc_} = build_degen(NbrAccSets),
%%  				 [ permute_ac(lists:seq(1,NbrAccSets),P,{DS_,[1],DTrs_,DAc_}) 
%%  				   || P <- permutations(lists:seq(1,NbrAccSets)) ] ++
 				 [ permute_ac(lists:seq(1,NbrAccSets),P,{DS_,[NbrAccSets+1],DTrs_,DAc_}) 
 				   || P <- permutations(lists:seq(1,NbrAccSets)) ]
%%  					 ++ 
%% 					 [{[1,2,3],[1],[{1,1,[1,2]},{1,3,[1]},{1,2,[]},
%% 									   {2,1,[1,2]},{2,3,[1]},{2,2,[]},
%% 									   {3,1,[2]},{3,3,[]}],[1]}]
		end,



%% 	B1 = buchi_reduce:remove_unnecessary_trans(synch_product({DS,[1],DTrs,DAc},{States,InitState,Trans})),
%%   	B2 = buchi_reduce:remove_unnecessary_trans(synch_product({DS,[NbrAccSets+1],DTrs,DAc},{States,InitState,Trans})),
%% 	Perms = permutations(DS2),
%% 	Degs = [ permute(DS2,Ps,{DS2,[1],DTrs2,DAc2}) || Ps <- Perms ] ++
%% 		[ permute(DS2,Ps,{DS2,[2],DTrs2,DAc2}) || Ps <- Perms ] ++
%% 		[ permute(DS2,Ps,{DS2,[NbrAccSets+1],DTrs2,DAc2}) || Ps <- Perms ],
%% 	Degs = [ permute(DS2,Ps,{DS2,[NbrAccSets+1],DTrs2,DAc2}) || Ps <- Perms ],
	prt_debug(3,"Degs: ~p\nGens: ~p\n",[Degs,Gens]), 
 	Bss  = [ synch_product(Ds,Gs) || Ds <- Degs, Gs <- Gens],
   	lists:foreach(fun({S,_,T,_}) ->
   						  prt_debug(3,"1Buchi automata: ~p states ~p transitions\n",
   									[length(S), length(T)])
   				  end,Bss),

  	Bss1  = [ buchi_reduce:reduce(B) || B <- Bss ],
   	lists:foreach(fun({S,_,T,_}) ->
   						  prt_debug(3,"2Buchi automata: ~p states ~p transitions\n",
   									[length(S), length(T)])
   				  end,Bss1),

%% 	Bss2 =
%% 		lists:sort(fun(B1,B2) ->
%% 						   buchi_reduce:size_of(B1) < buchi_reduce:size_of(B2)
%% 				   end,Bss1),
	
%%   	lists:foreach(fun({S,_,T,_}) ->
%%   						  prt_debug("3Buchi automata: ~p states ~p transitions\n",
%%   									[length(S), length(T)])
%%   				  end,Bss2),

%%  	prt_debug("Dss: ~p\nLTL2BDG: ~p\n~p\n",
%% 			  [lists:map(fun(D) ->
%% 								 permute([1,2,3],[1,2,0],D) end,Degs),
%%  			  [Degs,{DS,DTrs,DAc},permute_ac([0,1],[1,0],{DS,[0],DTrs,DAc})]),
%% 	hd(Bss2).
%% 	B1 = synch_product({DS,[1],DTrs,DAc},{States,InitState,Trans}),
%%   	B2 = synch_product({DS,[2],DTrs,DAc},{States,InitState,Trans}),
%% 	case buchi_reduce:size_of(B1) < buchi_reduce:size_of(B2) of
%% 		true -> B1;
%% 		false -> B2
%% 	end.		
	Bss.

synch_product({States1,InitStates1,Trans1, Accept1},{States2,InitStates2,Trans2}) ->
	%% 		States = [{S1,S2} || S1 <- States1,
	%% 												 S2 <- States2],
	InitStates = [{S1,S2} || S1 <- InitStates1,
							 S2 <- InitStates2],
	Trans = [{{T1,S21},{pick_best(Acc2,T1,Trans1),S22},Lbl} 
			 || {S21,S22,Lbl,Acc2} <- Trans2,
				T1 <- States1],
	Accept = [ {A,S} || A <- Accept1,
						S <- States2],
    Reachable = lists:usort(buchi_reduce:reachable(Trans,InitStates)),
	Trans_ = [Tr || Tr = {S1,_,_} <- Trans, lists:member(S1,Reachable)],
 	prt_debug(5,"Trans: ~p\nReach: ~p\n",[Trans_,Reachable]), 
	case Reachable of
		[] ->
			{[],[],[],[]};
		_ ->	StMap = lists:zip(Reachable,lists:seq(1,length(Reachable))),		
				MStates = lists:seq(1,length(Reachable)),
				MInitStates = [proplists:get_value(S,StMap) || S <- InitStates],
				MTrans  = lists:usort([{proplists:get_value(S1,StMap),
										proplists:get_value(S2,StMap),Lbl} 
									   || {S1,S2,Lbl} <- Trans, lists:member(S1,Reachable)]),
				MAccept = [proplists:get_value(A,StMap) 
						   || A <- Accept, lists:member(A,Reachable)],

				{MStates,MInitStates,MTrans,MAccept}
	end.

pick_best(Acc,N,Trans) ->
	Res = lists:reverse(
			lists:usort([ {lists:usort(Acc1),S2} || {S1,S2,Acc1} <- Trans,
													S1 == N, Acc1 -- Acc == []])),
   	prt_debug(5,"PB: ~w ==> ~w\n",[{Acc,N,Trans},Res]),
	element(2,hd(Res)).

build_degen(0) ->
	{[],[],[]};
build_degen(N) when N > 0 ->
	States = lists:seq(1,N+1),
	Trans  = [ {I,J,safe_seq(I,J-1)} || I <- safe_seq(1,N),
										J <- safe_seq(I+1,N+1)] ++
		[{I,I,[]} || I <- safe_seq(1,N)] ++
		[{N+1,N+1,lists:seq(1,N)}] ++
		lists:reverse([{N+1,I,safe_seq(1,I-1)} || I <- safe_seq(1,N)]),
	%%++ [{N+1,1,[]}] ,
	%% 		InitStates = [N+1],
	AcceptStates = [N+1],
	{States,Trans,AcceptStates}.

safe_seq(N,M) when M < N ->
	[];
safe_seq(N,M) ->
	lists:seq(N,M).


permute(Orig,New,{States,InitS,Trans,Accepts}) ->
	Map = lists:zip(Orig,New),
	{States,
	 [proplists:get_value(S,Map) || S <- InitS],
	 lists:usort([{proplists:get_value(S1,Map),proplists:get_value(S2,Map),L} || {S1,S2,L} <- Trans]),
	 [proplists:get_value(S,Map) || S <- Accepts]}.

permute_ac(Orig,New,{States,InitS,Trans,Accepts}) ->
	Map = lists:zip(Orig,New),
	{States,InitS,
	 lists:usort([{S1,S2,lists:map(fun(S) -> proplists:get_value(S,Map) end,L)} || {S1,S2,L} <- Trans]),
	 Accepts}.

permute_ac_gen(Orig,New,{States,Inits,Trans}) ->
	Map = lists:zip(Orig,New),
	{States,Inits,
	 [{S1,S2,Lbl,lists:usort(lists:map(fun(S) -> proplists:get_value(S,Map) end,L))} 
	  || {S1,S2,Lbl,L} <- Trans]}.
	

permutations([]) -> [[]];	 
permutations(Xs) ->
	[ [Y | Zs ]
	  || {Y,Ys} <- selections(Xs),
		 Zs <- permutations(Ys)].
	
selections([])->
	[];
selections([X | Xs]) ->
	[ {X,Xs} | [ {Y,[X|Ys]} || {Y,Ys} <- selections(Xs)]].


prt_debug(N,Str) ->
	prt_debug(N,Str,[]).

prt_debug(N,Str,Args) ->
	case N =< ?DEBUG of
		true -> io:format(Str,Args);
		false -> ok
	end.
			
