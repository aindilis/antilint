%%  Run:  swipl -g run_tests -t halt tests/test_antilint.pl
%%
%%  Rule and TMS tests build subjects directly from facts, so they need no
%%  packages or dpkg.  The extractor test writes a small tree to a temp
%%  directory.  Every test gets a fresh, empty, temporary data directory.

:- ensure_loaded('../lib/load').
:- use_module(library(plunit)).

fresh :-
    tmp_file(antilint_test, D),
    make_directory(D),
    setenv('ANTILINT_DATA', D),
    forall(vocab_pred(N/A), ( functor(H, N, A), retractall(H) )),
    forall(store_pred(N/A, _), ( functor(H, N, A), retractall(H) )),
    retractall(loaded_snapshot(_)),
    invalidate.

%%  snap(+S, +Pkg, +Attempt, +Facts): a loaded snapshot built in memory.
snap(S, Pkg, Att, Facts) :-
    assertz(subject(S, Pkg, Att)),
    forall(member(F, Facts), assertz(F)),
    assertz(loaded_snapshot(S)),
    invalidate.

judged(S, V, Src) :-
    get_time(T),
    remember(verdict(S, V, Src, test, T)).

w(R, S, Ws) :- unwaived_witnesses(R, S, Ws).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(core_rules).

test(al01_override, [setup(fresh)]) :-
    snap(s, val, 1, [debian_file(s, 'debian/val.lintian-overrides', 40, text),
                     debian_file(s, 'debian/rules', 40, text)]),
    w(al01, s, Ws),
    Ws == ['debian/val.lintian-overrides'].

test(al02_noop_and_unlisted, [setup(fresh)]) :-
    snap(s, souffle, 1, [patch_file(s, 'p.patch'), patch_hunks(s, 'p.patch', 0)]),
    w(al02a, s, ['p.patch']),
    w(al02b, s, ['p.patch']).

test(al02_real_patch_ok, [setup(fresh)]) :-
    snap(s, x, 1, [patch_file(s, 'p.patch'), patch_hunks(s, 'p.patch', 2),
                   series_entry(s, 'p.patch')]),
    w(al02a, s, []), w(al02b, s, []), w(al02c, s, []).

test(al03_fetch_and_comment, [setup(fresh)]) :-
    snap(s, leo, 1, [rules_line(s, 5, "\twget https://repo1.maven.org/x.jar"),
                     rules_line(s, 6, "# see https://example.org")]),
    w(al03a, s, [line(5, _)]).

test(al04_hollow, [setup(fresh)]) :-
    snap(s, fd, 1, [deb_built(s, fd),
                    deb_file(s, fd, '/usr/share/doc/fd/copyright', file),
                    deb_file(s, fd, '/usr/', dir)]),
    w(al04a, s, [fd]).

test(al04_not_hollow, [setup(fresh)]) :-
    snap(s, fd, 1, [deb_built(s, fd),
                    deb_file(s, fd, '/usr/share/doc/fd/copyright', file),
                    deb_file(s, fd, '/usr/bin/fast-downward', file)]),
    w(al04a, s, []).

test(al04_expected_missing, [setup(fresh)]) :-
    snap(s, fd, 1, [expected_artifact(s, '/usr/bin/fast-downward'),
                    deb_built(s, fd),
                    deb_file(s, fd, '/usr/bin/other', file)]),
    w(al04b, s, [missing('/usr/bin/fast-downward')]).

test(al05_masking, [setup(fresh)]) :-
    snap(s, x, 1, [rules_line(s, 1, "\tsbt assembly || true"),
                   rules_line(s, 2, "\trm -f foo || true"),
                   rules_line(s, 3, "\t\t-DBUILD_FOO=ON \\"),
                   rules_line(s, 4, "\t-$(MAKE) install")]),
    w(al05a, s, Ws),
    Ws == [line(1, "\tsbt assembly || true"), line(4, "\t-$(MAKE) install")].

test(al07_vendored, [setup(fresh)]) :-
    snap(s, x, 1, [vendored_dir(s, third_party),
                   vendored_dir(s, 'src/vendor'),
                   copyright_glob(s, '*'),
                   copyright_glob(s, 'third_party/*')]),
    w(al07a, s, ['src/vendor']).

test(unsafe_goal_rejected, [setup(fresh)]) :-
    catch(( safe_call(shell(ls)), fail ), error(unsafe_goal(_), _), true).

test(schema_validation, [setup(fresh)]) :-
    valid_schema(forbid_rules_substring(sbt)),
    \+ valid_schema(forbid_rules_substring(_)),
    \+ valid_schema(forbid_rules_substring(x)),
    \+ valid_schema(no_such_schema(abc)).

:- end_tests(core_rules).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(tms).

test(lifecycle, [setup(fresh)]) :-
    snap('val@1', val, 1, [rules_line('val@1', 5, "\tsbt assembly")]),
    judged('val@1', bad, human(andrew)),
    add_finding(val, andrew, 'sbt fetches at build time', F),
    propose(F, forbid_rules_substring(sbt), error, 'no sbt', 'use packaged jars', R),
    status(R, trial, _),
    effective_severity(R, warn),
    endorse(R, andrew),
    status(R, active, _),
    effective_severity(R, error),
    % a known-good package that legitimately says "sbt" demotes it
    snap('ok@gold', ok, gold, [rules_line('ok@gold', 3, "\t# sbt not used"),
                               rules_line('ok@gold', 4, "\tdh_sbt build")]),
    judged('ok@gold', good, gold(debian)),
    status(R, suspended, fires_on_good(['ok@gold'])),
    effective_severity(R, info),
    % withdrawing the only justification takes it OUT entirely
    retract_finding(F, 'misdiagnosed'),
    status(R, unsupported, _),
    effective_severity(R, off).

test(second_support_keeps_rule_in, [setup(fresh)]) :-
    snap('a@1', a, 1, [rules_line('a@1', 1, "\tgradle build")]),
    add_finding(a, andrew, one, F1),
    add_finding(a, reviewer, two, F2),
    propose(F1, forbid_rules_substring('gradle build'), error, t, h, R),
    propose(F2, forbid_rules_substring('gradle build'), error, t, h, R2),
    R2 == R,
    retract_finding(F1, wrong),
    \+ status(R, unsupported, _).

test(ineffective, [setup(fresh)]) :-
    snap('foo@1', foo, 1, [rules_line('foo@1', 1, "\tdh $@")]),
    add_finding(foo, andrew, 'something', F),
    propose(F, forbid_rules_substring(zzzz), error, t, h, R),
    status(R, ineffective, _).

test(veto_retires_core, [setup(fresh)]) :-
    veto(al08, andrew, 'too noisy for this archive'),
    status(al08, retired, _),
    effective_severity(al08, off).

test(waiver_suppresses_one_witness, [setup(fresh)]) :-
    snap('v@1', v, 1, [debian_file('v@1', 'debian/a.lintian-overrides', 1, text),
                       debian_file('v@1', 'debian/b.lintian-overrides', 1, text)]),
    waive(al01, v, 'debian/a.lintian-overrides', andrew, 'upstream bug 123'),
    w(al01, 'v@1', ['debian/b.lintian-overrides']).

test(persistence_round_trip, [setup(fresh)]) :-
    add_finding(p, andrew, text, F),
    propose(F, forbid_debian_file_glob('debian/*.jar'), error, t, h, R),
    load_store,
    learned_rule(R, forbid_debian_file_glob('debian/*.jar'), error, t, h, _),
    derived_from(R, F).

%%  generator_only: a human-maintained gold override is not evidence
%%  against al01, but a generated attempt judged good still is.
test(generator_only_gold_not_counterexample, [setup(fresh)]) :-
    snap('ep@gold', ep, gold, [debian_file('ep@gold', 'debian/ep.lintian-overrides', 1, text)]),
    judged('ep@gold', good, gold(debian)),
    status(al01, active, _).

test(generator_only_generated_good_counts, [setup(fresh)]) :-
    snap('g@1', g, 1, [debian_file('g@1', 'debian/g.lintian-overrides', 1, text)]),
    judged('g@1', good, human(andrew)),
    status(al01, disputed, _).

:- end_tests(tms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(learning).

gradle_bad(S, P) :-
    snap(S, P, 1, [rules_line(S, 1, "\t./gradlew shadowJar")]),
    judged(S, bad, human(andrew)).

test(induce_across_two_packages, [setup(fresh)]) :-
    gradle_bad('a@1', a),
    gradle_bad('b@1', b),
    snap('g@gold', g, gold, [rules_line('g@gold', 1, "\tdh $@ --with javahelper")]),
    judged('g@gold', good, gold(debian)),
    unexplained('a@1'),
    induce(2, 10, Created),
    Created \== [],
    learned_rule(R, forbid_rules_substring('./gradlew'), _, _, _, _),
    status(R, trial, _),
    effective_severity(R, warn).

test(induce_needs_support, [setup(fresh)]) :-
    gradle_bad('a@1', a),
    induce(2, 10, Created),
    Created == [].

test(repair_history, [setup(fresh)]) :-
    snap('x@1', x, 1, [debian_file('x@1', 'debian/x.lintian-overrides', 1, text)]),
    snap('x@2', x, 2, [debian_file('x@2', 'debian/rules', 1, text)]),
    judged('x@2', good, human(andrew)),
    previously_resolved(al01, [x]).

:- end_tests(learning).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(extract).

write_file(Root, Rel, Content) :-
    directory_file_path(Root, Rel, P),
    file_directory_name(P, Dir),
    make_directory_path(Dir),
    setup_call_cleanup(open(P, write, O), write(O, Content), close(O)).

test(tree, [setup(fresh)]) :-
    tmp_file(tree, Root),
    make_directory(Root),
    write_file(Root, 'debian/control', "Source: val\n\nPackage: val\nArchitecture: any\n"),
    write_file(Root, 'debian/rules', "#!/usr/bin/make -f\n%:\n\tdh $@\n\noverride_dh_auto_build:\n\tsbt assembly || true\n"),
    write_file(Root, 'debian/val.lintian-overrides', "val: no-changelog-file\n"),
    write_file(Root, 'debian/patches/series', "\n"),
    write_file(Root, 'debian/patches/0001-noop.patch', "Description: nothing\n---\n"),
    write_file(Root, 'debian/val/usr/bin/staged', "ignored: build staging\n"),
    write_file(Root, 'debian/copyright', "Files: *\nCopyright: x\n\nFiles: third_party/*\n extra/*\nCopyright: y\n"),
    write_file(Root, 'third_party/lib/a.c', "int a;\n"),
    extract('val@1', val, 1, Root, [debs-none]),
    binary_package('val@1', val),
    \+ debian_file('val@1', 'debian/val/usr/bin/staged', _, _),
    copyright_glob('val@1', 'extra/*'),
    vendored_dir('val@1', third_party),
    w(al01, 'val@1', ['debian/val.lintian-overrides']),
    w(al02a, 'val@1', ['0001-noop.patch']),
    w(al02b, 'val@1', ['0001-noop.patch']),
    w(al05a, 'val@1', [line(6, _)]),
    w(al07a, 'val@1', []).

:- end_tests(extract).
