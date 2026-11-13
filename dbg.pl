:- use_module(library(process)).
relation(_).
:- prolog_load_context(directory, Here), atom_concat(Here, '/build/detlog2-src', D), asserta(user:file_search_path(detlog2, D)).
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
:- initialization(dbg, main).
dbg :-
    forall(( member(F, ['src/algebra.pl', 'src/program.pl', 'src/aproof.pl', 'src/aplop2_cli.pl']),
             absolute_file_name(F, A),
             source_file(user:H, A), functor(H, N, Ar) ),
           ( trace(N/Ar, -all), trace(N/Ar, +fail) )),
    catch(program_cmd(af(nothing, nothing, nothing, []), "examples/sequences.pl", "sq/2"), E, (print_message(error, E))).
