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

%%% File    : ltl_rewrite.erl
%%% Author  : Hans Svensson <>
%%% Description : Rewrite(s) for ltl formulas
%%% Created : 19 Mar 2009 by Hans Svensson <>

-module(ltl_rewrite).

%-export([rewrite/1]).
-compile(export_all).

%%%
%% Pre-translation rewriting of LTL formula in the
%% spirit of Wring etc. (Eventually)
%%%
rewrite(Phi) ->
	SPhi = ltl:pnf(ltl2buchi:simplify(ltl:pnf(Phi))),
	s_rewrite(SPhi).

rew_rules() ->
		[{{lnot,ltrue}, lfalse},
		 {{lnot,lfalse}, ltrue},
		 %%AND
		 {{land,p,p},        p},
		 {{land,p,lfalse},   lfalse},
		 {{land,lfalse,p},   lfalse},
		 {{land,p,ltrue},    p},
		 {{land,ltrue,p},    p},
		 {{land,p,{lnot,p}}, lfalse},
		 {{land,{lnot,p},p}, lfalse},
		 %% OR
 		 {{lor,p,p},         p},
 		 {{lor,p,lfalse},    p},
 		 {{lor,lfalse,p},    p},
 		 {{lor,p,ltrue},     ltrue},
 		 {{lor,ltrue,p},     ltrue},
 		 {{lor,p,{lnot,p}},  ltrue},
 		 {{lor,{lnot,p},p},  ltrue},
		 
 		 {{until,{next,p},{next,q}}, {next,{until,p,q}}},
 
 		 {{land,{release,p,q},{release,p,r}}, {release,p,{land,q,r}}},
 		 {{lor,{release,p,r},{release,q,r}}, {release,{lor,p,q},r}},

 		 {{land,{next,p},{next,q}}, {next,{land,p,q}}},
		 
 		 {{next,ltrue}, ltrue},
 		 {{until,p,lfalse}, lfalse},

 		 {{lor,{always,{eventually,p}},{always,{eventually,q}}}, {always,{eventually,{lor,p,q}}}},
 		 {{eventually,{next,p}}, {next,{eventually,p}}},
 		 {{always,{always,{eventually,p}}}, {always,{eventually,p}}},
 		 {{eventually,{always,{eventually,p}}}, {always,{eventually,p}}},
 		 {{next,{always,{eventually,p}}}, {always,{eventually,p}}},
		 
 		 {{eventually,{land,p,{always,{eventually,q}}}}, {land,{eventually,p},{always,{eventually,q}}}},
 		 {{always,{lor,p,{always,{eventually,q}}}},      {lor,{always,p},{always,{eventually,q}}}},
 		 {{next,{land,p,{always,{eventually,q}}}},     {land,{next,p},{always,{eventually,q}}}},
 		 {{next,{lor,p,{always,{eventually,q}}}},      {lor,{next,p},{always,{eventually,q}}}}

		 %% Extra ones 
 		 ,{{eventually,{eventually,p}}, {eventually,p}}
%%  		 ,{{always,{always,p}}, {always,p}}
%%  		 ,{{lor,p,{eventually,p}}, {eventually,p}}
%%  		 ,{{lor,{eventually,p},p}, {eventually,p}}
%%  		 ,{{lor,{eventually,p},{always,p}}, {eventually,p}}
%%  		 ,{{lor,{eventually,p},{eventually,q}},{eventually,{lor,p,q}}}
%%  		 ,{{eventually,{next,{eventually,p}}}, {next,{eventually,p}}}
		].

s_rewrite(Phi) ->
%% 	io:format("Phi: ~s\n",[ltl:pp(Phi,java)]),
	Phi1 = s_rewrite1(Phi),
	NegPhi1 = ltl:pnf(ltl:lnot(Phi1)),
%% 	io:format("Phi1: ~s\n !--> ~s\n",[ltl:pp(Phi1,java),ltl:pp(NegPhi1,java)]),
	NegPhi2 = s_rewrite1(NegPhi1),
    Phi2 = s_rewrite1(ltl:pnf(ltl:lnot(NegPhi2))),
%% 	io:format("Phi2: ~s\n !--> ~s\n",[ltl:pp(NegPhi2,java),ltl:pp(Phi2,java)]),
	case Phi2 == Phi of
		true -> Phi;
		false -> s_rewrite(Phi2)
	end.

s_rewrite1(Phi) ->
	NPhi = apply_rules(Phi),
	case Phi == NPhi of
		false ->
			s_rewrite1(NPhi);
		true  ->
			case Phi of
				{lprop,_} -> Phi;
				{Op,Phi1} -> 
					NPhi1 = s_rewrite1(Phi1),
					case NPhi1 == Phi1 of
						false ->
							s_rewrite1({Op,NPhi1});
						true ->
							{Op,Phi1}
					end;
				{Op,Phi1,Phi2} -> 
					NPhi1 = s_rewrite1(Phi1),
					NPhi2 = s_rewrite1(Phi2),
					case (Phi1 == NPhi1) andalso
						 (Phi2 == NPhi2) of
						false ->
							s_rewrite1({Op,NPhi1,NPhi2});
						true ->
							{Op,Phi1,Phi2}
					end;
				ltrue ->
					ltrue;
				lfalse ->
					lfalse
			end
	end.

apply_rules(Phi) ->
	case match_rules(Phi) of
		false ->
%%  			io:format("No rule match: ~p\n",[Phi]),
			Phi;
		Rule ->
%%  			io:format("Rule match: ~p ~p\n",[Rule,Phi]),
			use_rule(Rule,Phi)
	end.
		 
use_rule({From,To}, Phi) ->
	Bindings = bind_vars(Phi,From),
	NPhi = insert_bindings(To,Bindings),
%% 	io:format("New formula: ~p\n",[NPhi]),
	NPhi.

match_rules(Phi) ->
	match_rules(Phi,simplify_rew_rules(rew_rules())).

match_rules(_Phi,[]) ->
	false;
match_rules(Phi,[Rule = {From,_To} | Rules]) ->
%%  	io:format("Trying: ~w on ~p\n",[From,Phi]),
	case match_rule(Phi,From) of
		true ->
			Binds = lists:usort(bind_vars(Phi,From)),
%% 			io:format("Temp match: ~w on ~p ==> ~w\n",[From,Phi,Binds]),
			case length(Binds) == length(lists:usort([P || {P,_} <- Binds])) of
				true ->	Rule;
				false -> match_rules(Phi,Rules)
			end;
		false ->
			match_rules(Phi,Rules)
	end.

match_rule(Phi,Rule) when is_tuple(Phi), is_tuple(Rule), tuple_size(Phi) /= tuple_size(Rule) ->
	false;
match_rule(Phi,Rule) when is_tuple(Phi), is_tuple(Rule) ->
	case {Phi,Rule} of
		{{Op1,P1,P2},{Op2,Q1,Q2}} ->
			(Op1 == Op2) andalso match_rule(P1,Q1) andalso match_rule(P2,Q2);
		{{Op1,P1},{Op2,Q1}} ->
			(Op1 == Op2) andalso match_rule(P1,Q1)
	end;
match_rule(Phi,Rule) when is_atom(Rule) -> 
	%% either Rule is p,q,r,s or ltrue/lfalse
	lists:member(Rule,[p,q,r,s]) orelse (Phi == Rule);
match_rule(_Phi,_Rule) ->
	false.

bind_vars(Phi,Rule) when is_tuple(Phi), is_tuple(Rule) ->
	case {Phi,Rule} of
		{{_,P1,P2},{_,Q1,Q2}} ->
			bind_vars(P1,Q1) ++ bind_vars(P2,Q2);
		{{_,P1},{_,Q1}} ->
			bind_vars(P1,Q1)
	end;
bind_vars(Phi,Rule) -> 
	%% either Rule is p,q,r,s or ltrue/lfalse
	case lists:member(Rule,[p,q,r,s]) of
		true ->
			[{Rule,Phi}];
		false ->
			[]
	end.

insert_bindings({Op,P1,P2},Env) ->
	{Op,insert_bindings(P1,Env),insert_bindings(P2,Env)};
insert_bindings({Op,P1},Env) ->
	{Op,insert_bindings(P1,Env)};
insert_bindings(P,Env) ->
	case proplists:get_value(P,Env) of
		undefined ->
			P;
		Val -> 
			Val
	end.
			

simplify_rew_rules(Rules) ->
	[{ltl2buchi:simplify(F),ltl2buchi:simplify(T)} || {F,T} <- Rules].

print_rules() ->
	lists:foreach(fun({From,To}) ->
						  io:format("~s ==> ~s\n",[ltl:pp(From),ltl:pp(To)])
				  end,rew_rules()).

print_simple_rules() ->
	lists:foreach(fun({From,To}) ->
						  io:format("~s ==> ~s\n",[ltl:pp(From),ltl:pp(To)])
				  end,simplify_rew_rules(rew_rules())).


%%%% Simple test examples
ltl1() ->
	ltl:land(
	  ltl:prop(x),
	  ltl:prop(x)).
ltl2() ->
	ltl:land(
	  ltl:lor(ltl:next(ltrue),ltl:prop(x)),
	  ltl:lor(ltl:prop(y),ltrue)).
ltl3() ->
	ltl:lor(
	  ltl:always(ltl:eventually(ltl:until(ltl:prop(a),ltl:prop(b)))),
	  ltl:always(ltl:eventually(ltl:prop(c)))).
