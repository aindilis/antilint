%%  report.pl -- what antilint says.

%%  violation(+S, -R, -Eff, -Witnesses)
violation(S, R, Eff, Ws) :-
    rule_id(R),
    effective_severity(R, Eff),
    Eff \== off,
    unwaived_witnesses(R, S, Ws),
    Ws \== [].

%%  report(+S, +Opts, -Errors)
report(S, Opts, NErr) :-
    findall(v(Rank, R, Eff, Ws),
            ( violation(S, R, Eff, Ws), sev_rank(Eff, R0), Rank is -R0 ),
            V0),
    msort(V0, Vs),
    aggregate_all(count, member(v(_, _, error, _), Vs), NErr),
    aggregate_all(count, member(v(_, _, warn, _), Vs), NWarn),
    aggregate_all(count, member(v(_, _, info, _), Vs), NInfo),
    findall(R-Ws, ( rule_id(R), waived_witnesses(R, S, Ws), Ws \== [] ), Waived),
    (   opt(json, Opts, false, true)
    ->  report_json(S, Vs, Waived, NErr, NWarn, NInfo)
    ;   report_text(S, Vs, Waived, NErr, NWarn, NInfo)
    ).

report_text(S, Vs, Waived, NErr, NWarn, NInfo) :-
    format("antilint: ~w~n", [S]),
    forall(member(v(_, R, Eff, Ws), Vs), print_violation(R, Eff, Ws)),
    forall(member(R-Ws, Waived),
           ( format("WAIVED ~w~n", [R]),
             forall(member(W, Ws), print_waiver(R, S, W)) )),
    format("---~nantilint: ~d error(s), ~d warning(s), ~d note(s)~n",
           [NErr, NWarn, NInfo]).

print_violation(R, Eff, Ws) :-
    rule(R, Origin, _, Title, _, Hint),
    status(R, St, _),
    sev_label(Eff, Label),
    origin_label(Origin, OL),
    format("~w ~w  ~w  [~w, ~w]~n", [Label, R, Title, OL, St]),
    forall(member(W, Ws), ( format("        ", []), print_witness(W), nl )),
    format("        hint: ~w~n", [Hint]),
    previously_resolved(R, Ps),
    (   Ps == [] -> true ; format("        previously fixed in: ~w~n", [Ps]) ).

print_waiver(R, S, W) :-
    subject(S, Pkg, _),
    waiver(R, PkgPat, WPat, Who, Why, _),
    ( PkgPat == '*' ; PkgPat == Pkg ),
    subsumes_term(WPat, W), !,
    format("        "), print_witness(W),
    format("  -- waived by ~w: ~w~n", [Who, Why]).
print_waiver(_, _, W) :-
    format("        "), print_witness(W), nl.

print_witness(line(L, T)) :- !,
    normalize_space(string(N), T),
    format("rules:~w: ~s", [L, N]).
print_witness(W) :-
    format("~w", [W]).

sev_label(error, 'ERROR').
sev_label(warn,  'WARN ').
sev_label(info,  'NOTE ').

origin_label(core, core) :- !.
origin_label(learned(Sch), L) :- format(atom(L), "learned ~q", [Sch]).

report_json(S, Vs, Waived, NErr, NWarn, NInfo) :-
    findall(D, ( member(v(_, R, Eff, Ws), Vs), violation_dict(R, Eff, Ws, D) ), Ds),
    findall(_{rule:R, witnesses:WS},
            ( member(R-Ws, Waived), maplist(witness_string, Ws, WS) ),
            WDs),
    json_write_dict(current_output,
                    _{subject:S, errors:NErr, warnings:NWarn, notes:NInfo,
                      violations:Ds, waived:WDs},
                    [width(0)]),
    nl.

violation_dict(R, Eff, Ws, _{rule:R, severity:Eff, status:St, title:Title,
                             witnesses:WS, hint:Hint, previously_fixed_in:Ps}) :-
    rule(R, _, _, Title, _, Hint),
    status(R, St, _),
    maplist(witness_string, Ws, WS),
    previously_resolved(R, Ps).

witness_string(line(L, T), Str) :- !,
    normalize_space(string(N), T),
    format(string(Str), "rules:~w: ~s", [L, N]).
witness_string(W, Str) :-
    format(string(Str), "~q", [W]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  antilint rules / why / unexplained / snapshots
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_rules :-
    format("~w~t~8|~w~t~16|~w~t~29|~w~t~36|~w~t~41|~w~n",
           [id, declared, status, effect, 'bad/good', title]),
    forall(rule_id(R),
           ( rule(R, _, Decl, Title, _, _),
             status(R, St, _),
             effective_severity(R, Eff),
             rule_counts(R, TPs, FPs),
             length(TPs, NT), length(FPs, NF),
             format(atom(C), "~d/~d", [NT, NF]),
             format("~w~t~8|~w~t~16|~w~t~29|~w~t~36|~w~t~41|~w~n",
                    [R, Decl, St, Eff, C, Title]) )).

why(R) :-
    must_be_rule(R),
    rule(R, Origin, Decl, Title, _, Hint),
    status(R, St, Why),
    effective_severity(R, Eff),
    rule_counts(R, TPs, FPs),
    format("~w: ~w~n", [R, Title]),
    origin_label(Origin, OL),
    format("  origin:    ~w~n", [OL]),
    format("  declared:  ~w~n", [Decl]),
    format("  status:    ~w   because ~q~n", [St, Why]),
    format("  effective: ~w~n", [Eff]),
    format("  fires on known-bad:  ~w~n", [TPs]),
    format("  fires on known-good: ~w~n", [FPs]),
    forall(derived_from(R, F), print_support(F)),
    forall(endorsed(R, Who, _), format("  endorsed by ~w~n", [Who])),
    forall(vetoed(R, Who, Reason, _), format("  vetoed by ~w: ~w~n", [Who, Reason])),
    forall(waiver(R, P, W, Who, Reason, _),
           format("  waiver: ~w ~q by ~w: ~w~n", [P, W, Who, Reason])),
    previously_resolved(R, Ps),
    (   Ps == [] -> true ; format("  previously fixed in: ~w~n", [Ps]) ),
    format("  hint: ~w~n", [Hint]).

print_support(F) :-
    (   finding(F, P, Who, Text, _)
    ->  (   retracted(F, RWhy, _)
        ->  format("  support ~w (~w, by ~w): ~w   [RETRACTED: ~w]~n",
                   [F, P, Who, Text, RWhy])
        ;   format("  support ~w (~w, by ~w): ~w~n", [F, P, Who, Text])
        )
    ;   format("  support ~w: (finding not found)~n", [F])
    ).

list_unexplained :-
    findall(S, unexplained(S), Ss),
    (   Ss == []
    ->  format("no coverage gaps: every artifact judged bad is caught by an error-level rule.~n")
    ;   format("judged bad, but no error-level rule fires (coverage gaps):~n"),
        forall(member(S, Ss), format("  ~w~n", [S]))
    ).

list_snapshots :-
    findall(S, loaded_snapshot(S), S0),
    sort(S0, Ss),
    forall(member(S, Ss),
           ( (   verdict_of(S, V) -> true ; V = unjudged ),
             format("~w~t~30|~w~n", [S, V]) )).

show_suggestions(S) :-
    (   loaded_snapshot(S) -> true
    ;   throw(antilint(no_such_snapshot(S)))
    ),
    suggest(S, Toks),
    (   Toks == []
    ->  format("nothing in ~w's debian/rules is absent from all known-good packaging.~n", [S])
    ;   format("text in ~w's debian/rules that no known-good package uses:~n", [S]),
        forall(member(T, Toks), format("  ~s~n", [T])),
        format("~nTo turn one into a rule, record a finding and propose it:~n"),
        subject(S, Pkg, _),
        format("  antilint finding ~w <you> '<what is wrong>'~n", [Pkg]),
        format("  antilint propose <finding-id> 'forbid_rules_substring(''<text>'')' error '<title>' '<hint>'~n")
    ).
