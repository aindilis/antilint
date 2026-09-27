%%  extract.pl -- turn a source tree, its .debs and its logs into facts.
%%
%%  extract(+Subject, +Pkg, +Attempt, +SourceDir, +Opts)
%%
%%  Opts (Key-Value pairs, all optional):
%%    debs-Dir|none   where to find .debs (default: parent of SourceDir,
%%                    restricted to binaries named in debian/control, and
%%                    to the newest .deb per binary)
%%    lintian-File    lintian output to parse
%%    'build-log'-File  build log to scan
%%    verify-pass|fail  verdict of verify_install
%%    expect-File     extra analysis-record file (expected_artifact/1 terms)
%%    deep-true       unpack each .deb and scan installed text files
%%
%%  The analysis record, if the generator wrote one, is read from
%%  SourceDir/.autopackager/analysis.pl: terms expected_artifact(Path).

extract(S, Pkg, Att, Src0, Opts) :-
    absolute_file_name(Src0, Src, [file_type(directory), access(read)]),
    directory_file_path(Src, debian, D),
    (   exists_directory(D) -> true
    ;   throw(antilint(no_debian_dir(Src)))
    ),
    clear_subject(S),
    assertz(subject(S, Pkg, Att)),
    extract_control(S, D),          % first: later steps need package names
    extract_debian_files(S, D),
    extract_patches(S, D),
    extract_rules(S, D),
    extract_copyright(S, D),
    extract_upstream(S, Src),
    extract_analysis(S, Src, Opts),
    extract_debs(S, Src, Opts),
    extract_logs(S, Opts).

opt(Key, Opts, Default, V) :-
    (   memberchk(Key-V0, Opts) -> V = V0 ; V = Default ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  File-system walking
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dir_entries(Dir, Es) :-
    catch(directory_files(Dir, All), _, fail),
    exclude(dot_entry, All, Es).

dot_entry('.').
dot_entry('..').

real_dir(P) :-
    exists_directory(P),
    \+ read_link(P, _, _).

entry(Dir, Prefix, E, Rel, Path) :-
    dir_entries(Dir, Es),
    member(E, Es),
    directory_file_path(Dir, E, Path),
    (   Prefix == '' -> Rel = E ; atomic_list_concat([Prefix, E], '/', Rel) ).

%%  file_under(+Dir, +Prefix, ?Depth, -Rel, -Path)
file_under(Dir, Prefix, Rel, Path) :-
    file_under(Dir, Prefix, 64, Rel, Path).

file_under(Dir, Prefix, Depth, Rel, Path) :-
    Depth > 0,
    entry(Dir, Prefix, E, R0, P0),
    (   real_dir(P0)
    ->  \+ skip_dir(E),
        D1 is Depth - 1,
        file_under(P0, R0, D1, Rel, Path)
    ;   exists_file(P0),
        Rel = R0,
        Path = P0
    ).

%%  dir_under(+Dir, +Prefix, +Depth, -Rel-Base)
dir_under(Dir, Prefix, Depth, Found) :-
    Depth > 0,
    entry(Dir, Prefix, E, R0, P0),
    real_dir(P0),
    \+ skip_dir(E),
    (   Found = R0-E
    ;   D1 is Depth - 1,
        dir_under(P0, R0, D1, Found)
    ).

skip_dir(E) :-
    memberchk(E, ['.git', '.pc', debian, '.svn', '.hg', '.autopackager',
                  target, '_build', build]), !.
skip_dir(E) :-
    sub_atom(E, 0, _, _, 'obj-').

file_lines(F, Lines) :-
    read_file_to_string(F, Str, [encoding(iso_latin_1)]),
    split_string(Str, "\n", "\r", Lines).

is_binary_file(F) :-
    setup_call_cleanup(open(F, read, In, [type(binary)]),
                       has_nul(In, 4096),
                       close(In)).

has_nul(In, N) :-
    N > 0,
    get_byte(In, B),
    B =\= -1,
    (   B =:= 0 -> true ; N1 is N - 1, has_nul(In, N1) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  debian/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

extract_control(S, D) :-
    directory_file_path(D, control, CF),
    (   exists_file(CF)
    ->  file_lines(CF, Ls),
        forall(( member(L, Ls),
                 sub_string(L, 0, 8, A, "Package:"),
                 sub_string(L, 8, A, 0, R),
                 normalize_space(atom(N), R),
                 N \== '' ),
               assert_once(binary_package(S, N)))
    ;   true
    ).

%%  Files the build writes into debian/ are not packaging and must not
%%  be judged as if the generator wrote them: staging trees (debian/tmp,
%%  debian/<binary>), debhelper state, substvars.
extract_debian_files(S, D) :-
    forall(( file_under(D, debian, Rel, Path),
             \+ build_artifact(S, Rel) ),
           ( size_file(Path, Size),
             (   is_binary_file(Path) -> K = binary ; K = text ),
             assertz(debian_file(S, Rel, Size, K)) )).

build_artifact(S, Rel) :-
    atomic_list_concat(Parts, '/', Rel),
    Parts = [debian, Top|Rest],
    (   Rest \== []
    ->  (   memberchk(Top, [tmp, '.debhelper'])
        ;   binary_package(S, Top)
        )
    ;   (   memberchk(Top, [files, 'debhelper-build-stamp'])
        ;   sub_atom(Top, _, _, 0, '.substvars')
        ;   sub_atom(Top, _, _, 0, '.debhelper.log')
        ;   sub_atom(Top, _, _, 0, '.debhelper')
        )
    ), !.

extract_patches(S, D) :-
    directory_file_path(D, patches, PD),
    (   exists_directory(PD)
    ->  directory_file_path(PD, series, SF),
        (   exists_file(SF)
        ->  file_lines(SF, SL),
            forall(( member(L, SL), series_name(L, N) ),
                   assert_once(series_entry(S, N)))
        ;   true
        ),
        forall(( file_under(PD, '', Rel, Path),
                 Rel \== series,
                 \+ sub_atom(Rel, _, _, 0, '~') ),
               extract_patch(S, Rel, Path))
    ;   true
    ).

series_name(L, N) :-
    normalize_space(string(T), L),
    T \== "",
    \+ sub_string(T, 0, 1, _, "#"),
    split_string(T, " ", "", [First|_]),
    atom_string(N, First).

extract_patch(S, Rel, Path) :-
    assertz(patch_file(S, Rel)),
    file_lines(Path, Ls),
    aggregate_all(count, ( member(L, Ls), sub_string(L, 0, 2, _, "@@") ), H),
    assertz(patch_hunks(S, Rel, H)),
    forall(( nextto(Minus, Plus, Ls),
             sub_string(Plus, 0, _, _, "+++ /dev/null"),
             sub_string(Minus, 0, 4, _, "--- "),
             deleted_path(Minus, P) ),
           assert_once(patch_deletes(S, Rel, P))).

deleted_path(Minus, P) :-
    sub_string(Minus, 4, _, 0, R0),
    split_string(R0, "\t", "", [R1|_]),
    normalize_space(atom(R2), R1),
    (   sub_atom(R2, 0, 2, _, 'a/') -> sub_atom(R2, 2, _, 0, P) ; P = R2 ).

extract_rules(S, D) :-
    directory_file_path(D, rules, RF),
    (   exists_file(RF)
    ->  file_lines(RF, Ls),
        forall(nth1(N, Ls, L), assertz(rules_line(S, N, L))),
        forall(test_disabled_in(Ls, How), assert_once(test_disabled(S, How)))
    ;   true
    ).

test_disabled_in(Ls, empty_test_override) :-
    nth1(N, Ls, L),
    sub_string(L, 0, _, _, "override_dh_auto_test"),
    N1 is N + 1,
    (   nth1(N1, Ls, Next) -> \+ sub_string(Next, 0, 1, _, "\t") ; true ).
test_disabled_in(Ls, forced_nocheck) :-
    member(L, Ls),
    sub_string(L, _, _, _, "DEB_BUILD_OPTIONS"),
    sub_string(L, _, _, _, "nocheck"),
    \+ sub_string(L, _, _, _, "filter"),       % the correct idiom tests for it
    (   sub_string(L, _, _, _, "+=") ; sub_string(L, _, _, _, "export") ).
test_disabled_in(Ls, cmake_testing_off) :-
    member(L, Ls),
    sub_string(L, _, _, _, "BUILD_TESTING=OFF").

extract_copyright(S, D) :-
    directory_file_path(D, copyright, CF),
    (   exists_file(CF)
    ->  file_lines(CF, Ls),
        copyright_globs(Ls, false, Gs),
        forall(member(G, Gs), assert_once(copyright_glob(S, G)))
    ;   true
    ).

copyright_globs([], _, []).
copyright_globs([L|Ls], In, Gs) :-
    (   sub_string(L, 0, 6, After, "Files:")
    ->  sub_string(L, 6, After, 0, Rest),
        glob_tokens(Rest, T),
        copyright_globs(Ls, true, G1),
        append(T, G1, Gs)
    ;   In == true, sub_string(L, 0, 1, _, " ")
    ->  glob_tokens(L, T),
        copyright_globs(Ls, true, G1),
        append(T, G1, Gs)
    ;   copyright_globs(Ls, false, Gs)
    ).

glob_tokens(Str, Atoms) :-
    split_string(Str, " \t", " \t", Parts),
    exclude(==(""), Parts, NonEmpty),
    maplist([P, A]>>atom_string(A, P), NonEmpty, Atoms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  Upstream tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

extract_upstream(S, Src) :-
    forall(( dir_under(Src, '', 3, Rel-Base), vendored_name(Base) ),
           assert_once(vendored_dir(S, Rel))),
    forall(( file_under(Src, '', 5, Rel, _), blob_file(Rel) ),
           assert_once(upstream_blob(S, Rel))).

vendored_name(B) :-
    downcase_atom(B, L),
    memberchk(L, [third_party, thirdparty, '3rdparty', vendor, vendored,
                  external, externals, extern, bundled, deps, node_modules]).

%%  Only formats an in-tree build does not normally produce, so that a
%%  tree extracted after building is not flooded with .o and .so files.
blob_file(Rel) :-
    file_name_extension(_, Ext0, Rel),
    downcase_atom(Ext0, Ext),
    memberchk(Ext, [jar, whl, dll, exe, dylib]).

extract_analysis(S, Src, Opts) :-
    directory_file_path(Src, '.autopackager/analysis.pl', A1),
    (   exists_file(A1) -> read_analysis(S, A1) ; true ),
    (   opt(expect, Opts, none, A2), A2 \== none
    ->  read_analysis(S, A2)
    ;   true
    ).

read_analysis(S, File) :-
    setup_call_cleanup(open(File, read, In),
                       read_analysis_terms(S, In),
                       close(In)).

read_analysis_terms(S, In) :-
    read_term(In, T, []),
    (   T == end_of_file
    ->  true
    ;   (   T = expected_artifact(P0), atomic(P0)
        ->  atom_string(P, P0), assert_once(expected_artifact(S, P))
        ;   true            % other analysis terms are for other tools
        ),
        read_analysis_terms(S, In)
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  .debs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

extract_debs(S, Src, Opts) :-
    opt(debs, Opts, default, DebOpt),
    (   DebOpt == none
    ->  true
    ;   (   DebOpt == default -> file_directory_name(Src, DebDir) ; DebDir = DebOpt ),
        findall(T-(Bin-P),
                ( dir_entries(DebDir, Es),
                  member(E, Es),
                  file_name_extension(_, deb, E),
                  deb_binary_name(E, Bin),
                  \+ sub_atom(Bin, _, _, 0, '-dbgsym'),
                  wanted_bin(S, Bin),
                  directory_file_path(DebDir, E, P),
                  time_file(P, T) ),
                Cands),
        findall(Bin, member(_-(Bin-_), Cands), Bs0),
        sort(Bs0, Bs),
        forall(member(B, Bs),
               ( findall(T-P, member(T-(B-P), Cands), TPs),
                 max_member(_-Newest, TPs),
                 extract_deb(S, B, Newest, Opts) ))
    ).

deb_binary_name(E, Bin) :-
    sub_atom(E, Before, _, _, '_'), !,
    sub_atom(E, 0, Before, _, Bin).

%%  With a control file, only its binaries count: the parent directory
%%  of a source tree often holds .debs from other packages.
wanted_bin(S, Bin) :-
    (   binary_package(S, _) -> binary_package(S, Bin) ; true ).

extract_deb(S, Bin, Deb, Opts) :-
    assert_once(deb_built(S, Bin)),
    process_lines(path('dpkg-deb'), ['-c', Deb], Lines),
    forall(( member(L, Lines), deb_line(L, Type, P) ),
           assert_once(deb_file(S, Bin, P, Type))),
    (   opt(deep, Opts, false, true) -> deep_scan(S, Bin, Deb) ; true ).

process_lines(Exe, Args, Lines) :-
    setup_call_cleanup(
        process_create(Exe, Args, [stdout(pipe(Out)), stderr(null), process(Pid)]),
        ( read_string(Out, _, Str), process_wait(Pid, _) ),
        close(Out)),
    split_string(Str, "\n", "", Lines0),
    exclude(==(""), Lines0, Lines).

%%  "-rwxr-xr-x root/root  1234 2026-09-19 12:00 ./usr/bin/foo"
deb_line(Line, Type, Path) :-
    split_string(Line, " ", " ", Parts0),
    exclude(==(""), Parts0, Parts),
    Parts = [Perm, _Owner, _Size, _Date, _Time, P0|_],
    sub_string(Perm, 0, 1, _, C),
    type_char(C, Type),
    (   sub_string(P0, 0, 1, _, ".") -> sub_string(P0, 1, _, 0, P1) ; P1 = P0 ),
    atom_string(Path, P1).

type_char("-", file) :- !.
type_char("d", dir) :- !.
type_char("l", link) :- !.
type_char(_, other).

hardcoded_needle("/home/").
hardcoded_needle("/root/").

deep_scan(S, Bin, Deb) :-
    tmp_file(antilint, Tmp),
    make_directory(Tmp),
    call_cleanup(
        ( process_lines(path('dpkg-deb'), ['-x', Deb, Tmp], _),
          forall(( file_under(Tmp, '', Rel, P),
                   size_file(P, Sz), Sz < 1048576,
                   \+ is_binary_file(P),
                   catch(read_file_to_string(P, Txt, [encoding(iso_latin_1)]), _, fail),
                   hardcoded_needle(N),
                   sub_string(Txt, _, _, _, N) ),
                 ( atom_concat('/', Rel, IP),
                   assert_once(installed_mention(S, Bin, IP, N)) )) ),
        delete_directory_and_contents(Tmp)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  Logs and oracle verdicts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

extract_logs(S, Opts) :-
    (   opt(lintian, Opts, none, LF), LF \== none
    ->  file_lines(LF, LLs),
        forall(( member(L, LLs), lintian_line(L, Sev, Tag) ),
               assert_once(lintian_tag(S, Sev, Tag)))
    ;   true
    ),
    (   opt('build-log', Opts, none, BF), BF \== none
    ->  file_lines(BF, BLs),
        forall(nth1(N, BLs, L), assertz(build_log_line(S, N, L)))
    ;   true
    ),
    (   opt(verify, Opts, none, V), V \== none
    ->  (   memberchk(V, [pass, fail])
        ->  assertz(verify_verdict(S, V))
        ;   throw(antilint(bad_verify_value(V)))
        )
    ;   true
    ).

%%  "E: val: no-changelog-file [usr/share/doc/val/]"
lintian_line(L, Sev, Tag) :-
    split_string(L, " ", "", [SevC, _PkgC, TagS|_]),
    string_length(SevC, 2),
    sub_string(SevC, 1, 1, 0, ":"),
    sub_string(SevC, 0, 1, _, SevS),
    atom_string(Sev, SevS),
    memberchk(Sev, ['E', 'W', 'I', 'P', 'X', 'O']),
    atom_string(Tag, TagS).
