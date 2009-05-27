-module(ltl_parse).
-export([string/1]).

-include_lib("eunit/include/eunit.hrl").

string(S) ->
    {ok, Toks, _} = erl_scan:string(S),
    %%   io:format("Tokens: ~p\n",[Ts]),
    LtlToks = ltl_scan(Toks),
    io:format("LtlTokens: ~p\n", [LtlToks]),
    {ok, Res} = ltl_parser:parse(LtlToks),
    Res.

ltl_scan([]) -> [];
ltl_scan([First| Rest]) ->
    case First of
		A = {atom, _N, _V} ->
			[A| ltl_scan(Rest)];
		{var, N, 'G'} ->
			[{always, N}| ltl_scan(Rest)];
		{var, N, 'F'} ->
			[{eventually, N}| ltl_scan(Rest)];
		{var, N, 'X'} ->
			[{next, N}| ltl_scan(Rest)];
		V = {var, _, _} ->
			[V| ltl_scan(Rest)];
		I = {integer, _, _} ->
			[I| ltl_scan(Rest)];
		{Sym, N} ->
			case lists:member(Sym, ltl_symbols()) of
				true ->
					[{map_ltl_symbol(Sym), N}| ltl_scan(Rest)];
				false ->
					case Sym of
						'[' ->
							Rest2 = ensure_rest(']', Rest),
							[{always, N}| ltl_scan(Rest2)];
						'<' ->
							Rest2 = ensure_rest('>', Rest),
							[{eventually, N}| ltl_scan(Rest2)];
						'<-' ->
							Rest2 = ensure_rest('>', Rest),
							[{equivalent, N}| ltl_scan(Rest2)];
						'<=' ->
							Rest2 = ensure_rest('>', Rest),
							[{equivalent, N}| ltl_scan(Rest2)];
						'&' ->
							case Rest of
								[{'&', _}| Rest2] ->
									[{'and', N}| ltl_scan(Rest2)];
								_ ->
									[{'and', N}| ltl_scan(Rest)]
							end;
						'=' ->
							case Rest of
								[{'>', _}| Rest2] ->
									[{implies, N}| ltl_scan(Rest2)];
								_ ->
									[{'=', N}| ltl_scan(Rest)]
							end;
						_ ->
							[Sym| ltl_scan(Rest)]
					end
			end;
		_ ->
			io:format("*** Error: token ~p not recognised~n", [First]),
			throw(bad_scan)
    end.

ensure_rest(Symbol,Tokens) ->
	case Tokens of
		[{Symbol,_}|RestTokens] ->
			RestTokens;
		_ ->
			io:format("*** Error: token ~p not found in ~p~n",[Symbol,Tokens]),
			throw(bad_scan)
	end.

ltl_symbols() ->
    ['+', '*', '!', '(', ')', '|', '||', 
	 '==', '->', '-', 'and', 'or', 'not'].

map_ltl_symbol('|') -> 'or';
map_ltl_symbol('||') -> 'or';
map_ltl_symbol('->') -> 'implies';
map_ltl_symbol('==') -> 'equivalent';
map_ltl_symbol('+') -> 'or';
map_ltl_symbol('*') -> 'and';
map_ltl_symbol('!') -> 'not';
map_ltl_symbol('-') -> 'not';
map_ltl_symbol(Symbol) -> Symbol.


%% Eunit tests

parse_simple_test_() ->
	[ ?_assert( string("p") =:= ltl:prop(p) ),
	  ?_assert( string("p=1") =:= ltl:prop(p) ),
	  ?_assert( string("! p") =:= ltl:lnot(ltl:prop(p))),
	  ?_assert( string("-p") =:= ltl:lnot(ltl:prop(p))),
	  ?_assert( string("G p") =:= ltl:always(ltl:prop(p))),
	  ?_assert( string("[] p") =:= ltl:always(ltl:prop(p))),
	  ?_assert( string("F p") =:= ltl:eventually(ltl:prop(p))),
	  ?_assert( string("<> p") =:= ltl:eventually(ltl:prop(p))),
	  ?_assert( string("X p") =:= ltl:next(ltl:prop(p))),

	  ?_assert( string("a & b") =:= ltl:land(ltl:prop(a),ltl:prop(b))),
	  ?_assert( string("a && b") =:= ltl:land(ltl:prop(a),ltl:prop(b))),

	  ?_assert( string("a | b") =:= ltl:lor(ltl:prop(a),ltl:prop(b))),
	  ?_assert( string("a || b") =:= ltl:lor(ltl:prop(a),ltl:prop(b))),

	  ?_assert( string("a -> b") =:= ltl:implication(ltl:prop(a),ltl:prop(b))),
	  ?_assert( string("a => b") =:= ltl:implication(ltl:prop(a),ltl:prop(b))),

	  ?_assert( string("a == b") =:= ltl:equivalent(ltl:prop(a),ltl:prop(b))),
	  ?_assert( string("a <-> b") =:= ltl:equivalent(ltl:prop(a),ltl:prop(b))),
	  ?_assert( string("a <=> b") =:= ltl:equivalent(ltl:prop(a),ltl:prop(b)))
	 ]. 



