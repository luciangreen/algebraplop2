/*  algebraplop2.pl - the algebraplop2 command line, in cut-free, choicepoint-free Prolog.

    swipl algebraplop2.pl COMMAND ARGS...          run from source
    swipl -o build/algebraplop2 -c algebraplop2.pl      build a saved state, then
    build/algebraplop2 COMMAND ARGS...

    algebraplop2 runs on detlog2's Prolog sources (its reader, interpreter,
    reference engine and cut elimination): DETLOG2_DIR, or ../detlog2, or
    build/detlog2-src (build.pl clones it there).

    The Haskell version this was ported from is in haskell/.
*/

:- use_module(library(process)).

relation(_).            % :- relation(Name/Arity) marks a relation (tools/cutfree.pl in detlog2)

:- relation(candidate_dir/2).

candidate_dir(_, D) :-
    getenv('DETLOG2_DIR', D).
candidate_dir(Here, D) :-
    atom_concat(Here, '/../detlog2', D),
    exists_directory(D).
candidate_dir(Here, D) :-
    atom_concat(Here, '/build/detlog2-src', D),
    exists_directory(D).

:- prolog_load_context(directory, Here),
   findall(D, candidate_dir(Here, D), [Dir|_]),
   asserta(user:file_search_path(detlog2, Dir)).

:- use_module(detlog2(src/detlog_runtime)).

:- ensure_loaded(detlog2(src/term)).
:- ensure_loaded(detlog2(src/stream)).
:- ensure_loaded(detlog2(src/reader)).
:- ensure_loaded(detlog2(src/pretty)).
:- ensure_loaded(detlog2(src/builtins)).
:- ensure_loaded(detlog2(src/prelude)).
:- ensure_loaded(detlog2(src/interp)).
:- ensure_loaded(detlog2(src/reference)).
:- ensure_loaded(detlog2(src/cut_elim)).

:- ensure_loaded(src/algebra).
:- ensure_loaded(src/program).
:- ensure_loaded(src/aproof).
:- ensure_loaded(src/aplop2_cli).

:- initialization(main, main).

main :-
    set_stream(user_output, encoding(utf8)),
    current_prolog_flag(argv, Argv),
    drop_dashdash(Argv, Args),
    catch(( cli(Args), flush_output ),
          cli_exit(Code),
          ( flush_output, halt(Code) )).

drop_dashdash([], []).
drop_dashdash([A|As], Out) :-
    if_commit(A == '--', Out = As, Out = [A|As]).
