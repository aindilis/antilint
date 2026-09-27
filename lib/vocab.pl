%%  vocab.pl -- the facts antilint reasons over.
%%
%%  Every extracted fact takes a SUBJECT as its first argument.  A subject
%%  is one attempt at one package, named Pkg@Attempt ('val@3',
%%  'souffle@gold').  Facts from many attempts, and from the known-good
%%  gold corpus, can therefore sit in memory together, and any rule can
%%  be backtested across all of them.  That is what makes learning
%%  possible: a rule is judged by where it fires.
%%
%%  Extracted facts are never persisted as knowledge.  They are either
%%  recomputed from the artifacts, or frozen in a snapshot file that is
%%  itself a record of what the artifacts looked like.

:- dynamic
    subject/3,            % subject(S, Pkg, Attempt)
    debian_file/4,        % debian_file(S, RelPath, Bytes, text|binary)
    series_entry/2,       % series_entry(S, PatchName)
    patch_file/2,         % patch_file(S, PatchName)
    patch_hunks/3,        % patch_hunks(S, PatchName, NumberOfHunks)
    patch_deletes/3,      % patch_deletes(S, PatchName, DeletedPath)
    rules_line/3,         % rules_line(S, LineNo, Text)          Text: string
    test_disabled/2,      % test_disabled(S, How)
    binary_package/2,     % binary_package(S, Name)   from debian/control
    deb_built/2,          % deb_built(S, BinaryName)  a .deb was found
    deb_file/4,           % deb_file(S, Bin, Path, file|dir|link|other)
    copyright_glob/2,     % copyright_glob(S, Glob)   from Files: fields
    vendored_dir/2,       % vendored_dir(S, RelDir)   upstream bundled code
    upstream_blob/2,      % upstream_blob(S, RelPath) prebuilt binary upstream
    expected_artifact/2,  % expected_artifact(S, Path) from the analysis record
    lintian_tag/3,        % lintian_tag(S, SevLetter, Tag)
    build_log_line/3,     % build_log_line(S, LineNo, Text)
    verify_verdict/2,     % verify_verdict(S, pass|fail)
    installed_mention/4.  % installed_mention(S, Bin, Path, Needle)  (--deep)

vocab_pred(subject/3).
vocab_pred(debian_file/4).
vocab_pred(series_entry/2).
vocab_pred(patch_file/2).
vocab_pred(patch_hunks/3).
vocab_pred(patch_deletes/3).
vocab_pred(rules_line/3).
vocab_pred(test_disabled/2).
vocab_pred(binary_package/2).
vocab_pred(deb_built/2).
vocab_pred(deb_file/4).
vocab_pred(copyright_glob/2).
vocab_pred(vendored_dir/2).
vocab_pred(upstream_blob/2).
vocab_pred(expected_artifact/2).
vocab_pred(lintian_tag/3).
vocab_pred(build_log_line/3).
vocab_pred(verify_verdict/2).
vocab_pred(installed_mention/4).

%%  clear_subject(+S)
%%  Forget everything extracted about S.
clear_subject(S) :-
    forall(vocab_pred(N/A),
           ( functor(H, N, A), arg(1, H, S), retractall(H) )).

%%  subject_facts(+S, -Facts)
%%  Every extracted fact about S, subject/3 first.
subject_facts(S, Facts) :-
    findall(H,
            ( vocab_pred(N/A), functor(H, N, A), arg(1, H, S), call(H) ),
            Facts).

assert_once(G) :-
    (   call(G) -> true ; assertz(G) ).
