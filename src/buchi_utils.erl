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
%% @doc Module containing utility functions for Buchi automata
%%
%% @type buchi_automaton(). A tuple structure representing a Buchi automaton.
%% @todo Use digraphs for representing Buchi automata.

-module(buchi_utils).

-export([size_of/1, reachable/1, reachable/2]).

%% @doc Size of Buchi automaton.
%% Returns a (bad) measure of the size of the BA
%% @spec (buchi_automaton()) -> int()
size_of({States,_InitStates,Trans,_Accepts}) ->
    length(States) + length(Trans).

%% A dfs...
%% @doc Return all reachable states of Buchi automaton.
%% Does a depth first traversal of the automaton.
%% @spec (buchi_automaton()) -> [state()]
reachable(_B = {_States,InitStates,Trans,_Accept}) ->
	reachable(Trans,InitStates).

%% @doc Return all reachable states given a set of transitions and the 
%% initial states.
%% @see reachable/1
%% @spec ([transition()],[state()]) -> [state()]
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

