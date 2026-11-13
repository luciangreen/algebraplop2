/*  cli.pl - end-to-end tests of the algebraplop2 command line (port of the Haskell
    tests/Cli.hs).

    swipl tests/cli.pl          (after building build/algebraplop2 and build/detlog2)

    Each test runs build/algebraplop2 (or build/detlog2) and looks at what it printed (standard
    output, then standard error) or at a file it wrote.
*/

:- use_module(library(process)).

relation(_).
:- relation(candidate_dir/2).

candidate_dir(_, D) :- getenv('DETLOG2_DIR', D).
candidate_dir(Here, D) :- atom_concat(Here, '/../../detlog2', D), exists_directory(D).
candidate_dir(Here, D) :- atom_concat(Here, '/../build/detlog2-src', D), exists_directory(D).

:- prolog_load_context(directory, Here), findall(D, candidate_dir(Here, D), [Dir|_]),
   asserta(user:file_search_path(detlog2, Dir)).

:- use_module(detlog2(src/detlog_runtime)).
:- initialization(main, main).

binary(aplop2, './build/algebraplop2').
binary(detlog2, './build/detlog2').

main :-
    actions(As),
    foldl(run_action, As, 0, Fails),
    format("~n"),
    compare(O, Fails, 0),
    finish(O, Fails).

finish(=, _) :-
    format("all CLI tests passed~n").
finish(>, N) :-
    format("~d CLI test(s) failed~n", [N]),
    halt(1).

out(Args, Text) :-
    out(aplop2, Args, Text).

out(Which, Args, Text) :-
    binary(Which, Bin),
    process_create(Bin, Args, [stdout(pipe(O)), stderr(pipe(E)), process(Pid)]),
    read_string(O, _, OS),
    read_string(E, _, ES),
    close(O),
    close(E),
    process_wait(Pid, _),
    string_concat(OS, ES, Text).

report(true, Name, _, F, F) :-
    format("PASS ~w~n", [Name]).
report(false, Name, Detail, F0, F) :-
    format("FAIL ~w~n", [Name]),
    split_string(Detail, "\n", "", Ls),
    forall_detail(Ls),
    F is F0 + 1.

forall_detail([]).
forall_detail([L|Ls]) :-
    format("    ~s~n", [L]),
    forall_detail(Ls).

contains(S, Sub, B) :-
    test_b(sub_string(S, _, _, _, Sub), B).

test_b(G, B) :-
    if_commit(G, B = true, B = false).

run_action(A, F0, F) :-
    action_kind(A, K),
    run_kind(K, A, F0, F).

action_kind(A, K) :-
    functor(A, K, _).

run_kind(expect, expect(Name, Want, Args), F0, F) :-
    out(Args, O),
    contains(O, Want, B),
    report(B, Name, O, F0, F).
run_kind(exact, exact(Name, Want, Args), F0, F) :-
    out(Args, O0),
    string_codes(O0, Cs),
    reverse(Cs, R),
    drop_newlines(R, R1),
    reverse(R1, Cs1),
    string_codes(O, Cs1),
    test_b(O == Want, B),
    format(string(D), "wanted:~n~s~ngot:~n~s", [Want, O]),
    report(B, Name, D, F0, F).
run_kind(file_has, file_has(Name, Want, Path), F0, F) :-
    read_file_to_string(Path, S, []),
    contains(S, Want, B),
    report(B, Name, S, F0, F).
run_kind(expect_d2, expect_d2(Name, Want, Args), F0, F) :-
    out(detlog2, Args, O),
    contains(O, Want, B),
    report(B, Name, O, F0, F).
run_kind(expect_not, expect_not(Name, Bad, Args), F0, F) :-
    out(Args, O),
    contains(O, Bad, B0),
    neg_bool(B0, B),
    report(B, Name, O, F0, F).
run_kind(run, run(Args), F, F) :-
    out(Args, _).
run_kind(code_free, code_free(Name, Path, Banned), F0, F) :-
    read_file_to_string(Path, S, []),
    split_string(S, "\n", "", Ls),
    findall(L, ( member(L, Ls), if_commit(sub_string(L, 0, 1, _, "%"), fail, true) ), Code),
    atomic_list_concat(Code, '\n', CA),
    atom_string(CA, CS),
    test_b(( member(X, Banned), sub_string(CS, _, _, _, X) ), Found),
    neg_bool(Found, B),
    report(B, Name, CS, F0, F).
run_kind(replace, replace(Src, Dst, Old, New), F, F) :-
    read_file_to_string(Src, S, []),
    replace_first(S, Old, New, S1),
    setup_call_cleanup(open(Dst, write, W, [encoding(utf8)]), write(W, S1), close(W)).
run_kind(mnns, mnns, F0, F) :-
    if_commit(( getenv('MNNS_DIR', Dir), absolute_file_name(path(swipl), _, [access(execute), file_errors(fail)]) ),
              run_action(expect('mnns AlgebraPLOp agrees', "mnns AlgebraPLOp: formula(linear(3,1)",
                                [samples, '1,4,7,10,13', '--mnns', Dir]),
                         F0, F),
              ( format("SKIP mnns comparison~n"), F = F0 )).

run_kind(write_file, write_file(Path, Text), F, F) :-
    run_kind_write(Path, Text).

neg_bool(true, false).
neg_bool(false, true).

drop_newlines([], []).
drop_newlines([C|Cs], Out) :-
    if_commit(C =:= 0'\n, drop_newlines(Cs, Out), Out = [C|Cs]).

replace_first(S, Old, New, S1) :-
    string_codes(S, Cs),
    string_codes(Old, OCs),
    string_codes(New, NCs),
    if_commit(( append(Before, Rest, Cs), append(OCs, After, Rest) ),
              ( conc(Before, NCs, P1), conc(P1, After, R), string_codes(S1, R) ),
              S1 = S).

conc([], L, L).
conc([X|Xs], L, [X|Ys]) :-
    conc(Xs, L, Ys).

actions([
  % discovery from samples
  expect('samples: 2,4,8,16 is 2 * 2^i', "formula: 2 * 2 ^ i", [samples, '2,4,8,16']),
  expect_not('samples: 2,4,8,16 is not piecewise', "periodic", [samples, '2,4,8,16']),
  expect('samples: affine', "formula: 1 + 3 * i", [samples, '1,4,7,10,13']),
  expect('samples: quadratic with a rational coefficient', "formula: (i + i * i) // 2", [samples, '0,1,3,6,10,15']),
  expect('samples: primes have no formula', "no_formula", [samples, '2,3,5,7,11']),
  expect('samples: too few samples for a held-out check', "no_formula", [samples, '5,9']),
  expect('samples: two indices', "formula: 2 * i + j", [samples, '[0,0]-0 [0,1]-1 [1,0]-2 [1,1]-3 [2,0]-4 [2,1]-5']),
  expect('samples: alternating', "periodic", [samples, '0,10,2,20,4,30,6,40']),
  expect('samples: proof', "proof accepted: fit", [samples, '1,4,7,10,13']),

  % formulas of programs
  expect('program: tri proved by induction', "proved(induction)", [program, 'examples/sequences.pl', 'tri/2']),
  expect('program: tri formula', "formula: tri/2 at position i = (i + i * i) // 2", [program, 'examples/sequences.pl', 'tri/2']),
  expect('program: pow2 proved', "proved(induction)", [program, 'examples/sequences.pl', 'pow2/2']),
  expect('program: sumsq proved (cubic)', "proved(induction)", [program, 'examples/sequences.pl', 'sumsq/2']),
  expect('program: grow proved (a b^n + c)', "proved(induction)", [program, 'examples/sequences.pl', 'grow/2']),
  expect('program: odd has an inverse', "inverse: odd__inverse(V, N)", [program, 'examples/sequences.pl', 'odd/2']),
  expect('program: sq only verified', "verified_on(", [program, 'examples/sequences.pl', 'sq/2', '--domain', '0..20']),
  expect('program: fib has no formula', "no_formula", [program, 'examples/sequences.pl', 'fib/2']),
  expect('program: loops replaced', "splice-index loops: 1", [program, 'examples/sequences.pl', 'tri/2']),

  run([program, 'examples/sequences.pl', 'tri/2', '-o', 'build/tri.pl']),
  expect('proof-check: accepted from files', "proof accepted",
         ['proof-check', 'examples/sequences.pl', 'build/tri.pl', 'build/tri.pl.proof']),
  replace('build/tri.pl', 'build/tri_bad.pl', "// 2", "// 3"),
  replace('build/tri.pl.proof', 'build/tri_bad.proof', "// 2", "// 3"),
  expect('proof-check: a wrong formula is rejected', "proof rejected",
         ['proof-check', 'examples/sequences.pl', 'build/tri_bad.pl', 'build/tri_bad.proof']),
  replace('build/tri.pl.proof', 'build/tri_bad2.proof', "m([1], 1 / 2)", "m([1], 3 / 2)"),
  expect('proof-check: a wrong formula term is rejected', "proof rejected",
         ['proof-check', 'examples/sequences.pl', 'build/tri.pl', 'build/tri_bad2.proof']),
  replace('examples/sequences.pl', 'build/other.pl', "T is T1 + N.", "T is T1 + N + 1."),
  expect('proof-check: another source is rejected', "proof rejected",
         ['proof-check', 'build/other.pl', 'build/tri.pl', 'build/tri.pl.proof']),
  expect_d2('detlog2 runs the formula', "V = 55.", [run, 'build/tri.pl', 'tri__formula(10, V)']),
  expect_d2('detlog2 runs the splice-index loop', "Ts = [1, 3, 6, 10].", [run, 'build/tri.pl', 'tris(1, 4, Ts)']),
  expect_d2('the formula keeps the domain', "false.", [run, 'build/tri.pl', 'tri__formula(-1, V)']),
  run([program, 'examples/sequences.pl', 'odd/2', '-o', 'build/odd.pl']),
  expect_d2('detlog2 runs the inverse', "N = 4.", [run, 'build/odd.pl', 'odd__inverse(9, N)']),
  expect_d2('inverse fails off the image', "false.", [run, 'build/odd.pl', 'odd__inverse(8, N)']),
  expect('proof-check: odd', "proof accepted", ['proof-check', 'examples/sequences.pl', 'build/odd.pl', 'build/odd.pl.proof']),

  mnns
]).
