%%  learn.pl -- how the rule base grows.
%%
%%  Three channels, in decreasing order of trust:
%%
%%   1. Review.  A human records a finding against a package; a human (or
%%      a model helping one) proposes a schema instance that would catch
%%      it.  propose/6 either creates a learned rule or, if the same rule
%%      already exists, adds the finding as a further justification.
%%
%%   2. Induction.  An artifact judged bad that no error-level rule
%%      explains is a COVERAGE GAP.  induce/3 looks for text in the
%%      debian/rules of such artifacts that never appears in known-good
%%      packaging, and asserts a forbid_rules_substring rule for any that
%%      recurs across at least MinPkgs distinct packages.  These rules are
%%      created automatically but can reach only `trial' (warn) without a
%%      human endorsement.
%%
%%   3. Repair history.  When a rule fired on attempt N of a package and
%%      not on a later attempt judged good, that package is a worked
%%      example of the fix.  Derived, not stored; shown with the hint.
%%
%%  None of these can edit a core rule, and no model output is ever
%%  written to the store directly.

%%  new_id(+Prefix, +ExistsGoal, -Id)
new_id(Prefix, Exists, Id) :-
    between(1, inf, N),
    atom_concat(Prefix, N, Id),
    \+ call(Exists, Id), !.

finding_exists(Id) :- finding(Id, _, _, _, _), !.
rule_exists(Id)    :- rule(Id, _, _, _, _, _), !.

add_finding(Pkg, Who, Text, Id) :-
    new_id(f, finding_exists, Id),
    get_time(T),
    remember(finding(Id, Pkg, Who, Text, T)).

retract_finding(Id, Why) :-
    (   finding_exists(Id) -> true ; throw(antilint(no_such_finding(Id))) ),
    get_time(T),
    remember(retracted(Id, Why, T)).

%%  propose(+FindingId, +RawSchema, +Severity, +Title, +Hint, -RuleId)
propose(FId, Raw, Sev, Title, Hint, RId) :-
    (   finding_exists(FId) -> true ; throw(antilint(no_such_finding(FId))) ),
    normalize_schema(Raw, Sch),
    (   valid_schema(Sch) -> true ; throw(antilint(invalid_schema(Raw))) ),
    (   valid_severity(Sev) -> true ; throw(antilint(invalid_severity(Sev))) ),
    (   learned_rule(Existing, Sch, _, _, _, _)
    ->  RId = Existing,
        (   derived_from(RId, FId) -> true ; remember(derived_from(RId, FId)) )
    ;   new_id(l, rule_exists, RId),
        get_time(T),
        remember(learned_rule(RId, Sch, Sev, Title, Hint, T)),
        remember(derived_from(RId, FId))
    ).

endorse(R, Who) :-
    must_be_rule(R),
    get_time(T),
    remember(endorsed(R, Who, T)).

veto(R, Who, Why) :-
    must_be_rule(R),
    get_time(T),
    remember(vetoed(R, Who, Why, T)).

%%  waive(+Rule, +Pkg|'*', +WitnessPattern, +Who, +Why)
%%  The replacement for lintian overrides: stored outside the package,
%%  attributed to a named human, visible in `why', never writable by the
%%  generator (it runs in the build VM and has no access to the store).
waive(R, Pkg, WPat, Who, Why) :-
    must_be_rule(R),
    get_time(T),
    remember(waiver(R, Pkg, WPat, Who, Why, T)).

judge(S, V, Who, Why) :-
    (   memberchk(V, [good, bad]) -> true ; throw(antilint(bad_verdict(V))) ),
    (   loaded_snapshot(S) -> true
    ;   format(user_error, "antilint: note: no snapshot for ~w yet; the verdict is kept and will apply once one exists~n", [S])
    ),
    get_time(T),
    remember(verdict(S, V, human(Who), Why, T)).

must_be_rule(R) :-
    (   rule_exists(R) -> true ; throw(antilint(no_such_rule(R))) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  Coverage gaps and induction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%  unexplained(-S): judged bad, yet no error-level rule fires on it.
unexplained(S) :-
    loaded_snapshot(S),
    bad_subject(S),
    \+ ( rule_id(R),
         effective_severity(R, error),
         fires_unwaived(R, S) ).

rules_token(S, Tok) :-
    rules_line(S, _, Line),
    \+ comment_line(Line),
    split_string(Line, " \t", " \t;()\"'", Parts),
    member(Tok, Parts),
    \+ trivial_token(Tok).

trivial_token(T) :-
    string_length(T, N), N < 3, !.
trivial_token(T) :-
    sub_string(T, 0, 1, _, F),
    memberchk(F, ["$", "#", "\\", "@", "="]), !.

%%  candidate_token(+S, -Tok): in S's rules, in no known-good rules.
candidate_token(S, Tok) :-
    rules_token(S, Tok),
    \+ ( good_subject(G), rules_token(G, Tok) ).

%%  suggest(+S, -Tokens)
suggest(S, Toks) :-
    findall(T, candidate_token(S, T), T0),
    sort(T0, Toks).

%%  induce(+MinPkgs, +Max, -Created)
induce(MinPkgs, Max, Created) :-
    findall(Tok-Pkg,
            ( unexplained(S),
              subject(S, Pkg, _),
              candidate_token(S, TokS),
              atom_string(Tok, TokS) ),
            P0),
    sort(P0, Pairs),
    findall(Tok, member(Tok-_, Pairs), T0),
    sort(T0, Toks),
    findall(NegN-(Tok-Pkgs),
            ( member(Tok, Toks),
              findall(P, member(Tok-P, Pairs), Pkgs),
              length(Pkgs, N),
              N >= MinPkgs,
              atom_length(Tok, TL), TL >= 2,
              \+ learned_rule(_, forbid_rules_substring(Tok), _, _, _, _),
              NegN is -N ),
            Ranked0),
    keysort(Ranked0, Ranked),
    findall(C, member(_-C, Ranked), Cands),
    take(Max, Cands, Chosen),
    findall(RId,
            ( member(Tok-Pkgs, Chosen),
              create_induced(Tok, Pkgs, RId) ),
            Created).

take(N, L, P) :-
    length(L, Len),
    (   Len =< N -> P = L ; length(P, N), append(P, _, L) ).

create_induced(Tok, Pkgs, RId) :-
    new_id(l, rule_exists, RId),
    get_time(T),
    format(atom(Title), 'debian/rules contains "~w" (induced)', [Tok]),
    atomic_list_concat(Pkgs, ', ', PkgList),
    format(atom(Hint),
           'Induced from failed attempts on ~w; this text never appears in known-good packaging. Work out what it does and remove the need for it.',
           [PkgList]),
    remember(learned_rule(RId, forbid_rules_substring(Tok), error, Title, Hint, T)),
    forall(member(P, Pkgs),
           ( format(atom(Text), 'induced: "~w" in debian/rules of a bad attempt', [Tok]),
             add_finding(P, auto, Text, F),
             remember(derived_from(RId, F)) )).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  Repair history
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%  previously_resolved(+R, -Pkgs)
%%  Packages where R fired on one attempt and not on a later attempt that
%%  was judged good.  Attempts should be integers so they order properly.
previously_resolved(R, Pkgs) :-
    findall(P,
            ( loaded_snapshot(S1), subject(S1, P, A1), A1 \== gold,
              fires_unwaived(R, S1),
              loaded_snapshot(S2), subject(S2, P, A2), A2 \== gold,
              A2 @> A1,
              good_subject(S2),
              \+ fires_unwaived(R, S2) ),
            P0),
    sort(P0, Pkgs).
