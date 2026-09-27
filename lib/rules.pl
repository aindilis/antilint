%%  rules.pl -- the negative specification.
%%
%%  A rule is reified as data:
%%
%%      rule(Id, Origin, DeclaredSeverity, Title, S-Witness-Condition, Hint)
%%
%%  Origin is `core' (written here, by hand) or learned(Schema) (read from
%%  the store).  Condition is run by safe_call/1 with the subject S bound;
%%  each solution yields one Witness -- the concrete thing that is wrong,
%%  which is what the model is shown.  Hint is the repair advice.
%%
%%  Declared severity is what the rule asks for.  What it GETS depends on
%%  its derived status (tms.pl): a learned rule on trial is capped at
%%  `warn' however it was declared.

valid_severity(error).
valid_severity(warn).
valid_severity(info).

rule(Id, core, Sev, Title, Cond, Hint) :-
    core_rule(Id, Sev, Title, Cond, Hint).
rule(Id, learned(Schema), Sev, Title, Cond, Hint) :-
    learned_rule(Id, Schema, Sev, Title, Hint, _),
    schema_cond(Schema, Cond).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  Core rules.  AL01-AL04 are the four defects found in the review of
%%  2026-09-19 (val, souffle, leo-iii, fast-downward).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

core_rule(al01, error, 'lintian override written by the generator',
    S-F-( debian_file(S, F, _, _),
          sub_atom(F, _, _, 0, 'lintian-overrides') ),
    'Delete the overrides file and repair the defect lintian reported. Lintian runs with --no-override, so an override cannot make the build pass.').

core_rule(al02a, error, 'patch with no hunks (no-op)',
    S-P-( patch_file(S, P), patch_hunks(S, P, 0) ),
    'A patch must change something. Either write the change the header describes, or delete the patch and its series entry.').

core_rule(al02b, error, 'patch not listed in series (never applied)',
    S-P-( patch_file(S, P), \+ series_entry(S, P) ),
    'Add the patch to debian/patches/series, or delete it if it is not needed.').

core_rule(al02c, error, 'series names a patch that does not exist',
    S-P-( series_entry(S, P), \+ patch_file(S, P) ),
    'Remove the entry from debian/patches/series or supply the patch.').

core_rule(al03a, error, 'network fetch in debian/rules',
    S-line(L, T)-( rules_line(S, L, T), network_fetch_line(T) ),
    'Builds must not use the network. Package the dependency, build-depend on it, or ship it as a separate orig tarball component.').

core_rule(al03b, warn, 'build log shows network activity',
    S-line(L, T)-( build_log_line(S, L, T), network_log_line(T) ),
    'Something in the build tried to reach the network. Find the step and make it offline.').

core_rule(al04a, error, 'hollow binary package (documentation only)',
    S-B-( deb_built(S, B),
          \+ ( deb_file(S, B, P, file), \+ doc_only_path(P) ) ),
    'The package installs nothing but documentation. Check the install step: expected build outputs were not found or not copied.').

core_rule(al04b, error, 'expected artifact missing from every .deb',
    S-missing(A)-( expected_artifact(S, A), \+ deb_file(S, _, A, _) ),
    'The analysis record says this file should be installed. Either install it or correct the analysis record, with a reason.').

core_rule(al04c, warn, 'binary package declared but no .deb built',
    S-B-( binary_package(S, B), any_deb_built(S), \+ deb_built(S, B) ),
    'debian/control declares this package but the build produced no .deb for it.').

core_rule(al05a, error, 'failure masked in debian/rules',
    S-line(L, T)-( rules_line(S, L, T), masking_line(T) ),
    'Do not hide failures with || true, 2>/dev/null or a leading -. If a step may legitimately fail, say why and test for the specific condition.').

core_rule(al05b, warn, 'existence-guarded install can silently ship nothing',
    S-line(L, T)-( rules_line(S, L, T), guarded_install_line(T) ),
    'Install unconditionally so a missing build output fails the build instead of producing an empty package.').

core_rule(al06a, error, 'large file in debian/',
    S-F-( debian_file(S, F, Size, _), Size > 65536 ),
    'debian/ holds packaging, not payload. Vendored code, jars and tarballs belong upstream or in a separate orig component.').

core_rule(al06b, error, 'binary file in debian/',
    S-F-( debian_file(S, F, _, binary) ),
    'Binary files do not belong in debian/. Generate them at build time or take them from upstream.').

core_rule(al07a, error, 'vendored directory not covered by debian/copyright',
    S-D-( vendored_dir(S, D), \+ copyright_covers(S, D) ),
    'Add a Files: stanza for the bundled code with its own copyright and licence. "Files: *" does not cover bundled third-party code.').

core_rule(al07b, warn, 'prebuilt binary in upstream tree not covered by debian/copyright',
    S-P-( upstream_blob(S, P), \+ copyright_covers(S, P) ),
    'Account for the prebuilt file: exclude it (Files-Excluded), build it from source, or document its licence.').

core_rule(al08, warn, 'upstream tests disabled',
    S-How-( test_disabled(S, How) ),
    'Run the upstream test suite. If a test cannot run in a build environment, disable that test alone and record why.').

core_rule(al09a, warn, 'build-host path in debian/rules',
    S-line(L, T)-( rules_line(S, L, T), build_host_path(T) ),
    'Use $(CURDIR) and debian/tmp paths, not paths from the machine that generated the packaging.').

core_rule(al09b, warn, 'installed file mentions a build-host path',
    S-(B:P:N)-( installed_mention(S, B, P, N) ),
    'An installed file embeds a path from the build machine. Configure the prefix correctly or patch the hard-coded path.').

core_rule(al10, warn, 'patch deletes a test file',
    S-(P:Path)-( patch_deletes(S, P, Path), test_like_path(Path) ),
    'Deleting a failing test hides the failure. Fix the cause, or skip the one test with a recorded reason.').

core_rule(al11, error, 'install verification failed',
    S-verify_install-( verify_verdict(S, fail) ),
    'The installed package does not run. See the verify_install output: wrong entry point, missing runtime dependency, or files in the wrong place.').

%%  generator_only(RuleId)
%%  Rules about what the GENERATOR may do, as opposed to what good
%%  packaging looks like.  Human-maintained gold packaging legitimately
%%  does these things with a recorded reason, so gold hits are not
%%  counterexamples (see counts_against/2 in tms.pl).  Add to this list
%%  only after looking at the gold witnesses, not in advance.
generator_only(al01).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  Helpers callable from conditions.  Trusted code.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

al_helper(comment_line/1).
al_helper(network_fetch_line/1).
al_helper(network_log_line/1).
al_helper(doc_only_path/1).
al_helper(any_deb_built/1).
al_helper(masking_line/1).
al_helper(guarded_install_line/1).
al_helper(copyright_covers/2).
al_helper(build_host_path/1).
al_helper(test_like_path/1).
al_helper(contains_text/2).

comment_line(T) :-
    normalize_space(string(N), T),
    sub_string(N, 0, 1, _, "#").

network_fetch_line(T) :-
    \+ comment_line(T),
    network_token(Tok),
    sub_string(T, _, _, _, Tok), !.

network_token("wget ").
network_token("curl ").
network_token("git clone").
network_token("pip install").
network_token("pip3 install").
network_token("npm install").
network_token("npm ci").
network_token("mvn ").
network_token("gradle ").
network_token("sbt ").
network_token("cargo fetch").
network_token("go get ").
network_token("go mod download").
network_token("http://").
network_token("https://").

network_log_line(T) :-
    network_log_token(Tok),
    sub_string(T, _, _, _, Tok), !.

network_log_token("Could not resolve host").
network_log_token("Temporary failure in name resolution").
network_log_token("Connecting to ").
network_log_token("Downloading from").
network_log_token("Downloading https://").
network_log_token("Network is unreachable").

doc_only_path(P) :-
    member(Pre, ['/usr/share/doc/', '/usr/share/doc-base/',
                 '/usr/share/lintian/', '/usr/share/man/']),
    sub_atom(P, 0, _, _, Pre), !.

any_deb_built(S) :-
    deb_built(S, _), !.

%%  masking_line(+Text)
%%  A recipe line that discards failure.  `rm -f x || true' in a clean
%%  target is the one common legitimate use, so rm/find lines are exempt;
%%  a make recipe line whose command starts with `-' also ignores errors.
masking_line(T) :-
    \+ comment_line(T),
    normalize_space(string(N), T),
    \+ benign_mask(N),
    (   member(M, ["|| true", "||true", "|| :", "2>/dev/null",
                   "2> /dev/null", "&>/dev/null"]),
        sub_string(N, _, _, _, M)
    ;   % make's ignore-errors prefix on a command.  Restricted to known
        % command starts, because option continuation lines such as
        % "-DBUILD_FOO=ON \" also begin with a dash.
        member(C, ["-$(", "-make", "-dh_", "-cp ", "-install ", "-mv ", "-ln "]),
        sub_string(N, 0, _, _, C)
    ), !.

benign_mask(N) :-
    member(P, ["rm ", "-rm ", "$(RM)", "find "]),
    sub_string(N, 0, _, _, P), !.

guarded_install_line(T) :-
    \+ comment_line(T),
    sub_string(T, _, _, _, "&&"),
    member(G, ["[ -f", "[ -e", "[ -x", "[ -d", "test -f", "test -e", "test -x"]),
    sub_string(T, _, _, _, G),
    member(C, ["cp ", "install ", "mv ", "dh_install"]),
    sub_string(T, _, _, _, C), !.

%%  copyright_covers(+S, +Path)
%%  Some Files: glob other than the bare "*" matches Path (a file) or
%%  anything under it (a directory).
copyright_covers(S, Path) :-
    copyright_glob(S, G),
    G \== '*',
    atomic_list_concat([Path, '/probe'], Probe),
    (   wildcard_match(G, Path)
    ;   wildcard_match(G, Probe)
    ;   sub_atom(G, 0, _, _, Path)
    ), !.

%%  contains_text(+Text, +Sub): Sub (atom or string) occurs in Text.
contains_text(T, Sub) :-
    atom_string(Sub, SubS),
    sub_string(T, _, _, _, SubS), !.

build_host_path(T) :-
    \+ comment_line(T),
    member(N, ["/home/", "/root/"]),
    sub_string(T, _, _, _, N), !.

test_like_path(P) :-
    downcase_atom(P, L),
    member(K, [test, spec, check]),
    sub_atom(L, _, _, _, K), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  Learnable rule schemas.
%%
%%  A learned rule is an INSTANCE of one of these templates with plain
%%  atom parameters.  Learning is therefore choosing a schema and filling
%%  in its slots, never writing clauses.  This is deliberate on two
%%  counts: it is safe (the store cannot hold arbitrary code), and it
%%  makes induction tractable (the hypothesis space is a few parameterised
%%  templates, not all of Prolog).  Add schemas here, by hand, when a
%%  human-found defect does not fit any existing one.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

schema(forbid_rules_substring(_),     'debian/rules must not contain this text').
schema(forbid_debian_file_glob(_),    'no file in debian/ may match this glob').
schema(forbid_patch_deleting_glob(_), 'no patch may delete a path matching this glob').
schema(forbid_build_log_substring(_), 'the build log must not contain this text').
schema(forbid_deb_path_glob(_),       'no installed file may match this glob').
schema(forbid_lintian_tag(_),         'this lintian tag must not appear at any severity').

schema_cond(forbid_rules_substring(Sub),
    S-line(L, T)-( rules_line(S, L, T), \+ comment_line(T),
                   contains_text(T, Sub) )).
schema_cond(forbid_debian_file_glob(G),
    S-F-( debian_file(S, F, _, _), wildcard_match(G, F) )).
schema_cond(forbid_patch_deleting_glob(G),
    S-(P:Path)-( patch_deletes(S, P, Path), wildcard_match(G, Path) )).
schema_cond(forbid_build_log_substring(Sub),
    S-line(L, T)-( build_log_line(S, L, T), contains_text(T, Sub) )).
schema_cond(forbid_deb_path_glob(G),
    S-(B:P)-( deb_file(S, B, P, file), wildcard_match(G, P) )).
schema_cond(forbid_lintian_tag(Tag),
    S-Tag-( lintian_tag(S, _, Tag) )).

%%  valid_schema(+Schema)
%%  Known schema, every parameter a non-trivial atom, expansion safe.
valid_schema(Sch) :-
    compound(Sch),
    \+ \+ schema(Sch, _),
    Sch =.. [_|Args],
    Args \== [],
    forall(member(A, Args), ( atom(A), atom_length(A, Len), Len >= 2 )),
    schema_cond(Sch, _-_-Cond),
    safe_goal(Cond).

%%  normalize_schema(+Raw, -Schema)
%%  Accept strings or code lists typed on the command line; store atoms.
normalize_schema(Raw, Sch) :-
    compound(Raw),
    Raw =.. [F|Args0],
    maplist(to_atom, Args0, Args),
    Sch =.. [F|Args].

to_atom(X, X) :- atom(X), !.
to_atom(X, A) :- string(X), !, atom_string(A, X).
to_atom(X, A) :- is_list(X), !, atom_codes(A, X).
to_atom(X, A) :- format(atom(A), "~w", [X]).
