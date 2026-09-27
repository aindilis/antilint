%%  tms.pl -- rule status as a justification-maintenance problem.
%%
%%  What is being maintained is not the fact base (extraction recomputes
%%  that every run) but BELIEF IN RULES: whether each rule should be
%%  enforced, and how hard.  That belief rests on justifications that can
%%  later be withdrawn, which is the situation a JTMS is for:
%%
%%    support     derived_from(Rule, Finding): the rule exists because a
%%                finding said this kind of thing is wrong.  Several
%%                findings may support one rule; it stays IN while any
%%                support is un-retracted.  Retract them all and the rule
%%                goes OUT (`unsupported') without anyone touching it.
%%    evidence    where the rule fires across snapshots, split by verdict:
%%                firing on a known-BAD artifact is weak positive evidence;
%%                firing on a known-GOOD artifact is a counterexample.
%%    authority   endorsed/3 (a named human vouches for it) and vetoed/4
%%                (a named human retires it).
%%
%%  Status is DERIVED, never stored, with a per-command cache.  The
%%  evaluation order below is the policy, and `antilint why RULE' prints
%%  which clause decided and on what grounds.
%%
%%  Statuses and the severity cap each imposes:
%%
%%    core rules:     active (error) | disputed (error, flagged) | retired
%%    learned rules:  retired      -- vetoed by a human            -> off
%%                    unsupported  -- every supporting finding
%%                                    has been retracted           -> off
%%                    suspended    -- fires on a known-good artifact -> info
%%                    ineffective  -- does not fire on the very
%%                                    package it was derived from  -> info
%%                    active       -- evidence and an endorsement  -> error
%%                    trial        -- evidence, no endorsement     -> warn
%%                    proposed     -- no evidence yet              -> info
%%
%%  The asymmetry is deliberate.  Evidence can raise a learned rule to
%%  `warn' on its own; only a named human can make it fail a build.  A
%%  single counterexample demotes it regardless of endorsement -- the fix
%%  is then a waiver for that artifact or a better rule, both of which
%%  leave a record.

:- dynamic status_cache/3.

invalidate :-
    retractall(status_cache(_, _, _)).

%%  Verdicts.  Precedence: human > gold > oracle; latest wins within one.

verdict_of(S, V) :-
    (   latest_verdict(S, human(_), V0) -> V = V0
    ;   latest_verdict(S, gold(_), V0)  -> V = V0
    ;   latest_verdict(S, oracle(_), V0) -> V = V0
    ).

latest_verdict(S, SrcPattern, V) :-
    findall(T-V1,
            ( verdict(S, V1, Src, _, T), subsumes_term(SrcPattern, Src) ),
            L),
    L \== [],
    max_member(_-V, L).

bad_subject(S)  :- verdict_of(S, bad).
good_subject(S) :- loaded_snapshot(S), verdict_of(S, good).

%%  Firing.

fires(R, S, W) :-
    rule(R, _, _, _, S-W-Cond, _),
    safe_call(Cond).

witnesses(R, S, Ws) :-
    (   setof(W, fires(R, S, W), Ws0) -> Ws = Ws0 ; Ws = [] ).

unwaived_witnesses(R, S, Ws) :-
    witnesses(R, S, All),
    exclude(waived(R, S), All, Ws).

waived_witnesses(R, S, Ws) :-
    witnesses(R, S, All),
    include(waived(R, S), All, Ws).

waived(R, S, W) :-
    subject(S, Pkg, _),
    waiver(R, PkgPat, WPat, _, _, _),
    (   PkgPat == '*' ; PkgPat == Pkg ),
    subsumes_term(WPat, W), !.

fires_unwaived(R, S) :-
    unwaived_witnesses(R, S, Ws),
    Ws \== [].

%%  rule_counts(+R, -BadHits, -GoodHits)
%%  Loaded snapshots the rule fires on, split by verdict.
rule_counts(R, TPs, FPs) :-
    findall(S, ( loaded_snapshot(S), fires_unwaived(R, S) ), F0),
    sort(F0, Fired),
    include(bad_subject, Fired, TPs),
    include(counts_against(R), Fired, FPs).

%%  counts_against(+R, +S): S is known-good, so R firing on it is a
%%  counterexample -- unless R is generator_only and S is gold.  Such
%%  rules encode distrust of the GENERATOR (an override the model wrote
%%  is gaming; one a Debian maintainer wrote, with a reason, is not), so
%%  human-maintained packaging is not evidence against them.  A generated
%%  attempt that a human judged good still counts.
counts_against(R, S) :-
    good_subject(S),
    \+ ( generator_only(R), subject(S, _, gold) ).

%%  status(+R, -Status, -Why)

status(R, St, Why) :-
    atom(R),
    (   status_cache(R, St0, W0)
    ->  true
    ;   compute_status(R, St0, W0),
        assertz(status_cache(R, St0, W0))
    ),
    St = St0,
    Why = W0.

compute_status(R, retired, vetoed(Who, Reason)) :-
    vetoed(R, Who, Reason, _), !.
compute_status(R, St, Why) :-
    core_rule(R, _, _, _, _), !,
    rule_counts(R, _, FPs),
    (   FPs == [] -> St = active, Why = core
    ;   St = disputed, Why = fires_on_good(FPs)
    ).
compute_status(R, unsupported, all_supports_retracted(Fs)) :-
    findall(F, derived_from(R, F), Fs),
    Fs \== [],
    forall(member(F, Fs), retracted(F, _, _)), !.
compute_status(R, St, Why) :-
    rule_counts(R, TPs, FPs),
    learned_status(R, TPs, FPs, St, Why).

learned_status(_, _, FPs, suspended, fires_on_good(FPs)) :-
    FPs \== [], !.
learned_status(R, _, _, ineffective, silent_on_own_support(Pkgs)) :-
    support_pkgs_with_snapshots(R, Pkgs),
    Pkgs \== [],
    \+ ( member(P, Pkgs), subject(S, P, _), loaded_snapshot(S), fires_unwaived(R, S) ), !.
learned_status(R, TPs, [], active, endorsed(Who, TPs)) :-
    TPs \== [],
    endorsed(R, Who, _), !.
learned_status(_, TPs, [], trial, evidence_only(TPs)) :-
    TPs \== [], !.
learned_status(_, _, _, proposed, no_evidence).

%%  Packages named by live (un-retracted) supporting findings, restricted
%%  to those we hold a snapshot for -- no snapshot, no test.
support_pkgs_with_snapshots(R, Pkgs) :-
    findall(P,
            ( derived_from(R, F),
              \+ retracted(F, _, _),
              finding(F, P, _, _, _),
              subject(S, P, _),
              loaded_snapshot(S) ),
            P0),
    sort(P0, Pkgs).

%%  Severity.

status_cap(active,      error).
status_cap(disputed,    error).
status_cap(trial,       warn).
status_cap(proposed,    info).
status_cap(ineffective, info).
status_cap(suspended,   info).
status_cap(unsupported, off).
status_cap(retired,     off).

sev_rank(off, 0).
sev_rank(info, 1).
sev_rank(warn, 2).
sev_rank(error, 3).

sev_min(A, B, M) :-
    sev_rank(A, RA),
    sev_rank(B, RB),
    (   RA =< RB -> M = A ; M = B ).

effective_severity(R, Eff) :-
    rule(R, _, Decl, _, _, _),
    status(R, St, _),
    status_cap(St, Cap),
    sev_min(Decl, Cap, Eff).

%%  Every rule id, once each, core first.
rule_id(R) :-
    findall(R0, core_rule(R0, _, _, _, _), Cs),
    findall(R0, learned_rule(R0, _, _, _, _, _), Ls),
    append(Cs, Ls, All),
    member(R, All).
