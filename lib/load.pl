%%  load.pl -- load every part of antilint, in dependency order.
%%
%%  Plain files consulted into `user', like queue.pl, rather than
%%  modules: the program is small, and one namespace keeps the rule
%%  conditions (which are data) free of module qualification.

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).
:- use_module(library(process)).
:- use_module(library(filesex)).
:- use_module(library(http/json)).

:- ensure_loaded(vocab).     % the facts rules reason over
:- ensure_loaded(safe).      % whitelisting interpreter for rule conditions
:- ensure_loaded(store).     % persistence: data dir, append-only files, snapshots
:- ensure_loaded(rules).     % core rules, helpers, learnable rule schemas
:- ensure_loaded(extract).   % source tree + .debs + logs  ->  vocab facts
:- ensure_loaded(tms).       % derived rule status, justifications, severity
:- ensure_loaded(learn).     % findings, proposals, induction, repair history
:- ensure_loaded(report).    % text and JSON output

startup :-
    load_store,
    load_snapshots,
    invalidate.
