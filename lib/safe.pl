%%  safe.pl -- run rule conditions without trusting them.
%%
%%  Rule conditions are data.  Core rules are written by hand, but learned
%%  rules are read from files that a process (or, one day, a model) may
%%  have written.  A condition may therefore call only:
%%
%%    - vocabulary facts (vocab_pred/1),
%%    - trusted helpers defined in rules.pl (al_helper/1),
%%    - a short list of side-effect-free builtins (safe_builtin/1),
%%    - control: ',', ';', '->', '\+', true.
%%
%%  Anything else raises error(unsafe_goal(G), _).  There is no shell, no
%%  assert, no file access, no call/N reachable from a condition.

safe_builtin(true/0).
safe_builtin(fail/0).
safe_builtin((=)/2).
safe_builtin((\=)/2).
safe_builtin((==)/2).
safe_builtin((\==)/2).
safe_builtin((<)/2).
safe_builtin((>)/2).
safe_builtin((=<)/2).
safe_builtin((>=)/2).
safe_builtin((=:=)/2).
safe_builtin(is/2).
safe_builtin(sub_atom/5).
safe_builtin(sub_string/5).
safe_builtin(wildcard_match/2).
safe_builtin(atom_concat/3).
safe_builtin(string_concat/3).
safe_builtin(atom_string/2).
safe_builtin(atom_length/2).
safe_builtin(string_length/2).
safe_builtin(downcase_atom/2).
safe_builtin(string_lower/2).
safe_builtin(member/2).
safe_builtin(memberchk/2).
safe_builtin(between/3).
safe_builtin(atomic_list_concat/3).

safe_call(G) :-
    var(G), !,
    instantiation_error(G).
safe_call(true) :- !.
safe_call((A, B)) :- !,
    safe_call(A),
    safe_call(B).
safe_call((C -> T ; E)) :- !,
    (   safe_call(C) -> safe_call(T) ; safe_call(E) ).
safe_call((A ; B)) :- !,
    (   safe_call(A) ; safe_call(B) ).
safe_call((C -> T)) :- !,
    (   safe_call(C) -> safe_call(T) ).
safe_call(\+ G) :- !,
    \+ safe_call(G).
safe_call(G) :-
    callable(G),
    functor(G, N, A),
    permitted(N/A), !,
    call(G).
safe_call(G) :-
    throw(error(unsafe_goal(G), _)).

permitted(PI) :- vocab_pred(PI), !.
permitted(PI) :- al_helper(PI), !.
permitted(PI) :- safe_builtin(PI).

%%  safe_goal(+G)
%%  Static check: G only mentions permitted goals.  Used to vet schema
%%  expansions before they are ever run.
safe_goal(G) :- var(G), !, fail.
safe_goal(true) :- !.
safe_goal((A, B)) :- !, safe_goal(A), safe_goal(B).
safe_goal((A ; B)) :- !, safe_goal(A), safe_goal(B).
safe_goal((A -> B)) :- !, safe_goal(A), safe_goal(B).
safe_goal(\+ G) :- !, safe_goal(G).
safe_goal(G) :- callable(G), functor(G, N, A), permitted(N/A).
