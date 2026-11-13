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
st(G) :- ( catch(G, E, (print_message(error, E), fail)) -> format(user_error, "ok ~q~n", [G]) ; format(user_error, "FAIL ~q~n", [G]), halt(1) ).
dbg :-
    st(load_program("examples/sequences.pl", Src)),
    Key = sq/2, P = sq,
    st(extract_recurrence(Src, Key, MRec)),
    st(sample_predicate(Src, Key, 0, 12, right(Samples))),
    st(discover(Samples, just(found(F, _, _, _)))),
    Lo = 0, Hi = 12,
    st(formula_clause(P, F, Lo, just(Hi), FormulaC)),
    st(key_t(Key, KT)), st(formula_term(F, FT)), st(clause_t(FormulaC, FCT)),
    EvidenceStep = comp(exhaustive, [KT, int(Lo), int(Hi), FT, FCT]),
    Evidence = comp(verified_on, [comp('..', [int(Lo), int(Hi)])]),
    st(all_src_clauses(Src, AllSrc)),
    st(loop_clause(P, LoopC)),
    st(expr_term(F, [atom(i)], ExprT)),
    RSpec = comp(r_spec, [KT, comp(position, [int(1)]), comp(value, [int(2)]), comp(formula, [FT]), comp(expression, [ExprT]), Evidence]),
    Steps = [EvidenceStep, RSpec],
    st(max_var_id(RSpec, MV)), RNV is MV + 1,
    st(concat_lists([AllSrc, [FormulaC], [clause(RSpec, atom(true), RNV)]], OutClauses)),
    st(program_from_clauses(OutClauses, OutProg)),
    st(maplist(proved_step(Src), Steps, _)),
    st(step_shape(EvidenceStep, Name)),
    st(key_of(KT, Key1)),
    st(formula_of(FT, F1)),
    st(ap_as_clause(FCT, Cl)),
    st(formula_clause(P, F1, Lo, just(Hi), Want)),
    st(ap_variant(Cl, Want)),
    st(exhaustive_go(Lo, Hi, Src, Key1, "k", F1)),
    st(sample_agree(Src, Key1, Cl, Lo, Hi)),
    st(justified_step(Src, Steps, OutProg, [], EvidenceStep, _)),
    st(check_algebra_proof(Src, Steps, OutProg, _)),
    LoopC = LoopC, Name = Name, LoopC = _.
