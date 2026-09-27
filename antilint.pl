#!/usr/bin/env swipl
%%  antilint -- what an autopackaged Debian package must never contain or do.
%%
%%  Companion to autopackager and packaging-queue.  It is a separate
%%  program on purpose: the queue is a scheduler, and this is a judge.
%%  autopackager calls it after lintian and treats a non-zero exit as a
%%  failed build; the queue sees only the resulting attempt outcome.
%%
%%  Copyright (C) 2026 Andrew Dougherty.  GPL-3.0-or-later.

:- ensure_loaded(lib/load).

:- initialization(main, main).

%%  Exit status is set by the command and applied only after the catch:
%%  recent SWI-Prolog implements halt/1 by unwinding, which a catch-all
%%  around dispatch/1 would otherwise intercept.
main :-
    current_prolog_flag(argv, Argv),
    nb_setval(antilint_exit, 0),
    (   catch(dispatch(Argv), E, ( report_error(E), nb_setval(antilint_exit, 2) ))
    ->  true
    ;   format(user_error, "antilint: command failed~n", []),
        nb_setval(antilint_exit, 2)
    ),
    nb_getval(antilint_exit, Code),
    halt(Code).

report_error(antilint(E)) :- !,
    format(user_error, "antilint: ~q~n", [E]).
report_error(usage(E)) :- !,
    format(user_error, "antilint: ~q~n~n", [E]),
    usage(user_error).
report_error(E) :-
    message_to_codes_safe(E, Msg),
    format(user_error, "antilint: ~s~n", [Msg]).

message_to_codes_safe(E, Msg) :-
    catch(( message_to_codes(E, _, Msg0), Msg = Msg0 ), _,
          format(codes(Msg), "~q", [E])).

usage(S) :-
    format(S, "usage: antilint COMMAND ...~n~n", []),
    forall(usage_line(L), format(S, "  ~w~n", [L])).

usage_line('check SRC [--pkg P] [--attempt N] [--debs DIR|none] [--lintian F]').
usage_line('          [--build-log F] [--verify pass|fail] [--expect F] [--deep]').
usage_line('          [--snapshot] [--json]          judge one attempt; exit 1 on error').
usage_line('gold SRC [--pkg P]                       snapshot known-good packaging').
usage_line('judge SUBJECT good|bad WHO [WHY]         record a human verdict (pkg@attempt)').
usage_line('rules                                    all rules, derived status, evidence').
usage_line('why RULE                                 justification for a rule''s status').
usage_line('snapshots                                snapshots and their verdicts').
usage_line('unexplained                              bad artifacts no error rule catches').
usage_line('finding PKG WHO TEXT                     record a review finding').
usage_line('retract FINDING WHY                      withdraw a finding').
usage_line('propose FINDING SCHEMA SEV TITLE HINT    learn a rule from a finding').
usage_line('endorse RULE WHO                         let a learned rule fail builds').
usage_line('veto RULE WHO WHY                        retire a rule').
usage_line('waive RULE PKG|* WHO WHY [WITNESS]       human exception, recorded').
usage_line('suggest SUBJECT                          candidate rule text for a gap').
usage_line('induce [--min N] [--max N]               auto-propose rules from gaps').
usage_line('schemas                                  learnable rule templates').

dispatch([]) :- !, usage(user_output).
dispatch([help|_]) :- !, usage(user_output).
dispatch([Cmd|Args0]) :-
    parse_args(Args0, Pos, Opts),
    startup,
    command(Cmd, Pos, Opts).

parse_args([], [], []).
parse_args([A|As], Pos, Opts) :-
    atom_concat('--', Key, A), !,
    (   flag_opt(Key)
    ->  Opts = [Key-true|Os],
        parse_args(As, Pos, Os)
    ;   As = [V|As1]
    ->  Opts = [Key-V|Os],
        parse_args(As1, Pos, Os)
    ;   throw(usage(missing_value(A)))
    ).
parse_args([A|As], [A|Pos], Opts) :-
    parse_args(As, Pos, Opts).

flag_opt(json).
flag_opt(snapshot).
flag_opt(deep).

command(check, [Src], Opts) :- !,
    package_name(Src, Opts, Pkg),
    attempt_id(Opts, Att),
    format(atom(S), '~w@~w', [Pkg, Att]),
    extract(S, Pkg, Att, Src, Opts),
    (   opt(snapshot, Opts, false, true)
    ->  save_snapshot(S),
        (   verify_verdict(S, fail)
        ->  get_time(T),
            remember(verdict(S, bad, oracle(verify_install), 'verify_install failed', T))
        ;   true            % passing verification is NOT a good verdict
        )
    ;   true
    ),
    invalidate,
    report(S, Opts, NErr),
    (   NErr > 0 -> nb_setval(antilint_exit, 1) ; true ).
command(gold, [Src], Opts) :- !,
    package_name(Src, Opts, Pkg),
    format(atom(S), '~w@gold', [Pkg]),
    extract(S, Pkg, gold, Src, [debs-none|Opts]),
    save_snapshot(S),
    get_time(T),
    remember(verdict(S, good, gold(debian), 'known-good packaging', T)),
    format("snapshotted ~w as known-good~n", [S]).
command(judge, [S, V, Who|Why0], _) :- !,
    atomic_list_concat(Why0, ' ', Why),
    judge(S, V, Who, Why),
    format("~w judged ~w by ~w~n", [S, V, Who]).
command(rules, [], _) :- !, list_rules.
command(why, [R], _) :- !, why(R).
command(snapshots, [], _) :- !, list_snapshots.
command(unexplained, [], _) :- !, list_unexplained.
command(finding, [Pkg, Who|Words], _) :- !,
    (   Words == [] -> throw(usage(finding_needs_text)) ; true ),
    atomic_list_concat(Words, ' ', Text),
    add_finding(Pkg, Who, Text, Id),
    format("~w~n", [Id]).
command(retract, [F|Words], _) :- !,
    atomic_list_concat(Words, ' ', Why),
    retract_finding(F, Why),
    format("retracted ~w~n", [F]).
command(propose, [F, SchText, Sev, Title, Hint], _) :- !,
    catch(term_string(Raw, SchText), _, throw(antilint(unparseable_schema(SchText)))),
    propose(F, Raw, Sev, Title, Hint, R),
    invalidate,
    status(R, St, Why),
    format("~w: ~w (~q)~n", [R, St, Why]).
command(endorse, [R, Who], _) :- !,
    endorse(R, Who),
    status(R, St, _),
    format("~w endorsed by ~w; status now ~w~n", [R, Who, St]).
command(veto, [R, Who|Words], _) :- !,
    atomic_list_concat(Words, ' ', Why),
    veto(R, Who, Why),
    format("~w retired~n", [R]).
command(waive, [R, Pkg, Who, Why|Rest], _) :- !,
    (   Rest = [WText]
    ->  term_string(WPat, WText)
    ;   Rest == []
    ->  true                % unbound pattern: every witness
    ;   throw(usage(too_many_arguments))
    ),
    waive(R, Pkg, WPat, Who, Why),
    format("waiver recorded~n").
command(suggest, [S], _) :- !, show_suggestions(S).
command(induce, [], Opts) :- !,
    opt(min, Opts, '2', Min0), atom_number(Min0, Min),
    opt(max, Opts, '5', Max0), atom_number(Max0, Max),
    induce(Min, Max, Created),
    (   Created == []
    ->  format("no rule met the support threshold (--min ~d)~n", [Min])
    ;   forall(member(R, Created),
               ( rule(R, _, _, Title, _, _), status(R, St, _),
                 format("~w  ~w  [~w]~n", [R, Title, St]) ))
    ).
command(schemas, [], _) :- !,
    forall(schema(Sch, Desc),
           ( functor(Sch, N, A), format("~w/~w~t~32|~w~n", [N, A, Desc]) )).
command(Cmd, Pos, _) :-
    throw(usage(bad_command([Cmd|Pos]))).

%%  Package name: --pkg, else the source name in debian/changelog, else
%%  the directory name.
package_name(_, Opts, Pkg) :-
    opt(pkg, Opts, none, Pkg), Pkg \== none, !.
package_name(Src, _, Pkg) :-
    directory_file_path(Src, 'debian/changelog', CL),
    exists_file(CL),
    file_lines(CL, [First|_]),
    split_string(First, " ", "", [NameS|_]),
    NameS \== "", !,
    atom_string(Pkg, NameS).
package_name(Src, _, Pkg) :-
    absolute_file_name(Src, Abs),
    file_base_name(Abs, Pkg).

%%  Attempt: --attempt (as an integer if it is one), else the time.
attempt_id(Opts, Att) :-
    (   opt(attempt, Opts, none, A0), A0 \== none
    ->  (   atom_number(A0, N), integer(N) -> Att = N ; Att = A0 )
    ;   get_time(T), Att is floor(T)
    ).
