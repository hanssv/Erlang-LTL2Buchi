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
%% @doc Module defining Büchi automata
%%
%% @type buchi_automaton(). A tuple structure representing a Büchi automaton.
%% @todo Use digraphs for representing Büchi automata.

-module(buchi).

-export([is_buchi/1
		 empty_buchi/0,
		 is_empty/1,
		 intersection/2, 
		 ltl_intersection/2, 
		 buchi2digraph/1]).

-define(BUCHI_IMPL,buchi_tuple).


%% True if the BA has its labels in the states
%% @doc Recognize labelled Büchi automaton.
%% @spec (buchi_automaton()) -> bool()
is_buchi(B) -> ?BUCHI_IMPL:is_buchi(B).

%% The empty BA
%% @doc The empty non-labeled Büchi automaton.
%% @spec () -> buchi_automaton()
empty_buchi() -> ?BUCHI_IMPL:empty_buchi().

%% Empty check
%% @doc Check Büchi automaton for emptiness.
%% @spec (buchi_automaton()) -> bool()
is_empty(B) -> ?BUCHI_IMPL:is_empty(B).

%% @doc Intersection of two Büchi automata.
%% Computes the product/intersection of two BA's,
%% the result is a non-generalized, non-labeled BA.
%% @spec (buchi_automaton(),buchi_automaton()) -> buchi_automaton()
intersection(B1,B2) -> ?BUCHI_IMPL:intersection(B1,B2).

%% @doc LTL intersection of Büchi automaton and LTL 
%% formula translated to Büchi automaton. 
%% The first BA is a System model (or an automata generated
%% from a witness) and the second BA is generated from an 
%% LTL formula. Maybe this operation has a better name!??
%% @spec (buchi_automaton(),buchi_automaton()) -> buchi_automaton()
ltl_intersection(B1,B2) -> ?BUCHI_IMPL:ltl_intersection(B1,B2).

%% Build buichi-digraph
%% @doc Translate  Büchi automaton into digraph.
%% @see //stdlib/digraph. digraph
%% @spec (buchi_automaton()) -> digraph()
buchi2digraph(B) -> ?BUCHI_IMPL:buchi2digraph(B).
