%%  store.pl -- what antilint remembers between runs.
%%
%%  Everything here is an append-only record of an EVENT: a rule was
%%  learned, a finding was made, a human judged an artifact, endorsed or
%%  vetoed a rule, granted a waiver.  Nothing here is a STATUS.  Rule
%%  status is derived on every query from these events and the snapshots
%%  (tms.pl), the same discipline queue.pl follows for package state.
%%  Consequence: correcting the record never requires editing a status,
%%  only adding an event, and `antilint why' can always show its work.
%%
%%  Data directory: $ANTILINT_DATA, else data/ beside antilint.pl.
%%  Keep it under version control, in a repository of its own: it is
%%  local judgement history, not part of antilint.

:- dynamic
    learned_rule/6,   % learned_rule(Id, Schema, DeclaredSev, Title, Hint, Time)
    derived_from/2,   % derived_from(RuleId, FindingId)     a justification
    finding/5,        % finding(Id, Pkg, Who, Text, Time)
    retracted/3,      % retracted(FindingId, Why, Time)
    verdict/5,        % verdict(Subject, good|bad, Source, Why, Time)
                      %   Source: human(Who) | gold(Where) | oracle(Name)
    endorsed/3,       % endorsed(RuleId, Who, Time)
    vetoed/4,         % vetoed(RuleId, Who, Why, Time)
    waiver/6,         % waiver(RuleId, Pkg|'*', WitnessPattern, Who, Why, Time)
    loaded_snapshot/1.% in memory only: snapshot subjects currently loaded

store_pred(learned_rule/6, 'learned_rules.pl').
store_pred(derived_from/2, 'learned_rules.pl').
store_pred(finding/5,      'findings.pl').
store_pred(retracted/3,    'findings.pl').
store_pred(verdict/5,      'verdicts.pl').
store_pred(endorsed/3,     'decisions.pl').
store_pred(vetoed/4,       'decisions.pl').
store_pred(waiver/6,       'decisions.pl').

:- dynamic antilint_lib_dir/1.
:- prolog_load_context(directory, D),
   retractall(antilint_lib_dir(_)),
   assertz(antilint_lib_dir(D)).

data_dir(Dir) :-
    (   getenv('ANTILINT_DATA', D), D \== ''
    ->  Dir = D
    ;   antilint_lib_dir(L),
        file_directory_name(L, Home),
        directory_file_path(Home, data, Dir)
    ).

ensure_data_dir :-
    data_dir(D),
    make_directory_path(D),
    directory_file_path(D, snapshots, SD),
    make_directory_path(SD).

%%  remember(+Event)
%%  Assert and append one event.  The only way the store changes.
remember(Term) :-
    functor(Term, N, A),
    (   store_pred(N/A, File) -> true
    ;   throw(error(domain_error(store_event, Term), _))
    ),
    (   admissible(Term) -> true
    ;   throw(error(domain_error(admissible_event, Term), _))
    ),
    assertz(Term),
    ensure_data_dir,
    data_dir(D),
    directory_file_path(D, File, Path),
    setup_call_cleanup(open(Path, append, Out, [encoding(utf8)]),
                       format(Out, "~q.~n", [Term]),
                       close(Out)),
    invalidate.

%%  admissible(+Event)
%%  Learned rules are schema instances with plain-atom parameters, never
%%  arbitrary clauses.  Checked on write and again on load, so a
%%  hand-edited or corrupted file cannot smuggle in a goal.
admissible(learned_rule(Id, Schema, Sev, _, _, _)) :- !,
    atom(Id),
    valid_schema(Schema),
    valid_severity(Sev).
admissible(_).

load_store :-
    forall(store_pred(N/A, _),
           ( functor(H, N, A), retractall(H) )),
    ensure_data_dir,
    data_dir(D),
    findall(F, store_pred(_, F), Fs0),
    sort(Fs0, Fs),
    forall(member(F, Fs),
           ( directory_file_path(D, F, P),
             (   exists_file(P) -> load_terms(P, store) ; true ) )).

load_terms(Path, Mode) :-
    setup_call_cleanup(open(Path, read, In, [encoding(utf8)]),
                       read_terms(In, Path, Mode),
                       close(In)).

read_terms(In, Path, Mode) :-
    catch(read_term(In, T, []), E,
          ( format(user_error, "antilint: unreadable term in ~w: ~q~n", [Path, E]),
            T = end_of_file )),
    (   T == end_of_file
    ->  true
    ;   accept_term(Mode, Path, T),
        read_terms(In, Path, Mode)
    ).

accept_term(store, Path, T) :-
    functor(T, N, A),
    (   store_pred(N/A, _)
    ->  (   admissible(T)
        ->  assertz(T)
        ;   format(user_error, "antilint: rejected inadmissible ~q in ~w~n", [T, Path])
        )
    ;   format(user_error, "antilint: ignoring unknown term ~q in ~w~n", [T, Path])
    ).
accept_term(snapshot, Path, T) :-
    functor(T, N, A),
    (   vocab_pred(N/A)
    ->  assertz(T)
    ;   format(user_error, "antilint: ignoring non-vocabulary term ~q in ~w~n", [T, Path])
    ).

%%  Snapshots: frozen extractions, one file per subject.

snapshot_path(S, P) :-
    data_dir(D),
    directory_file_path(D, snapshots, SD),
    atom_concat(S, '.pl', F),
    directory_file_path(SD, F, P).

save_snapshot(S) :-
    ensure_data_dir,
    snapshot_path(S, P),
    subject_facts(S, Fs),
    setup_call_cleanup(open(P, write, Out, [encoding(utf8)]),
                       forall(member(F, Fs), format(Out, "~q.~n", [F])),
                       close(Out)),
    assert_once(loaded_snapshot(S)),
    invalidate.

load_snapshots :-
    retractall(loaded_snapshot(_)),
    ensure_data_dir,
    data_dir(D),
    directory_file_path(D, snapshots, SD),
    directory_files(SD, Es),
    forall(( member(E, Es), file_name_extension(Base, pl, E), Base \== '' ),
           ( clear_subject(Base),
             directory_file_path(SD, E, P),
             load_terms(P, snapshot),
             (   subject(Base, _, _)
             ->  assert_once(loaded_snapshot(Base))
             ;   format(user_error, "antilint: snapshot ~w has no subject/3 fact; skipped~n", [E])
             ) )),
    invalidate.
