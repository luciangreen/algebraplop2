/*  aplop2_cli.pl - the algebraplop2 commands (port of the Haskell
    app/Main.hs).

    Commands write to the current output and to user_error.  die/1 writes
    "algebraplop2: Message" to user_error and throws cli_exit(1).
*/

usage_text(T) :-
    atomic_list_concat([
      "algebraplop2 - positional formulas, inverses and splice-index loops, with proofs",
      "",
      "  algebraplop2 samples SAMPLES [--mnns DIR]",
      "        SAMPLES: values at positions 0, 1, ... (\"2,4,8,16\") or position-value",
      "        pairs (\"[0,0]-1 [0,1]-2 [1,0]-3 ...\"); prints the formula or no_formula",
      "  algebraplop2 program FILE NAME/2 [--domain LO..HI] [--mnns DIR] [-o OUT]",
      "        the formula of NAME(Position, Value): proved by induction when NAME is a",
      "        first-order recurrence, else verified on LO..HI; writes NAME__formula,",
      "        NAME__inverse (affine formulas), NAME__loop for findall/between loops,",
      "        and r_spec facts",
      "  algebraplop2 proof-check FILE OUT OUT.proof",
      "",
      "Every output is proof-gated: it is written only if AlgebraPLOp2.Proof accepts its proof.",
      ""], '\n', T).

die(Msg) :-
    format(user_error, "algebraplop2: ~w~n", [Msg]),
    throw(cli_exit(1)).

% ---------------------------------------------------------------------------
% Flags: af(Domain, Mnns, Out, PositionalRev)

parse_flags(Args, E) :-
    catch(( flags_go(Args, af(nothing, nothing, nothing, []), F), E = right(F) ),
          flag_error(M), E = left(M)).

flags_go([], af(D, Mn, O, P), af(D, Mn, O, P1)) :-
    rev(P, P1).
flags_go([A|As], F0, F) :-
    atom_string(A, AS),
    flag_kind(AS, As, K),
    flag_step(K, AS, As, F0, F).

flag_kind(AS, As, K) :-
    if_commit(( AS == "--domain", As = [_|_] ), K = domain,
    if_commit(( AS == "--mnns", As = [_|_] ), K = mnns,
    if_commit(( AS == "-o", As = [_|_] ), K = out,
    if_commit(string_concat("--", _, AS), K = unknown,
              K = positional)))).

flag_step(domain, _, [X|R], af(_, Mn, O, P), F) :-
    atom_string(X, XS),
    if_commit(( sub_string(XS, B, 2, _, ".."), split_domain(XS, B, Lo, Hi) ),
              flags_go(R, af(just(Lo-Hi), Mn, O, P), F),
              throw(flag_error("--domain expects LO..HI"))).
flag_step(mnns, _, [X|R], af(D, _, O, P), F) :-
    atom_string(X, XS),
    flags_go(R, af(D, just(XS), O, P), F).
flag_step(out, _, [X|R], af(D, Mn, _, P), F) :-
    atom_string(X, XS),
    flags_go(R, af(D, Mn, just(XS), P), F).
flag_step(unknown, AS, _, _, _) :-
    string_concat("unknown option ", AS, M),
    throw(flag_error(M)).
flag_step(positional, AS, R, af(D, Mn, O, P), F) :-
    flags_go(R, af(D, Mn, O, [AS|P]), F).

split_domain(XS, B, Lo, Hi) :-
    once_det(sub_string(XS, 0, B, _, LoS)),
    if_commit(sub_string(LoS, _, _, _, "."), fail, true),
    B2 is B + 2,
    once_det(sub_string(XS, B2, _, 0, HiS)),
    read_int(LoS, Lo),
    read_int(HiS, Hi).

read_int(X, N) :-
    if_commit(catch(number_string(N0, X), _, fail), N = N0, throw(flag_error("Prelude.read: no parse"))).

fl_domain(af(D, _, _, _), D).
fl_mnns(af(_, Mn, _, _), Mn).
fl_out(af(_, _, O, _), O).
fl_pos(af(_, _, _, P), P).

% ---------------------------------------------------------------------------

cli([]) :-
    usage_text(T),
    write(T).
cli([Cmd|Rest]) :-
    if_commit(Cmd == help,
              ( usage_text(T), write(T) ),
              ( parse_flags(Rest, E),
                cli_flags(E, Cmd) )).

cli_flags(left(M), _) :-
    die(M).
cli_flags(right(Fl), Cmd) :-
    fl_pos(Fl, Pos),
    atom_string(Cmd, CS),
    if_commit(dispatch_known(CS, Pos), dispatch(CS, Pos, Fl), bad_arguments).

bad_arguments :-
    usage_text(U),
    string_concat("bad arguments\n", U, M),
    die(M).

dispatch_known("samples", [_|_]).
dispatch_known("program", [_, _]).
dispatch_known("proof-check", [_, _, _]).

dispatch("samples", Ws, Fl) :-
    atomic_list_concat(Ws, ' ', WA),
    atom_string(WA, W),
    parse_samples(W, SE),
    if_commit(SE = right(Samples), true, ( SE = left(SM), die(SM) )),
    discover(Samples, MF),
    if_commit(MF = just(found(F, _, Held, Pen)),
              ( samples_t(Samples, ST),
                formula_term(F, FT),
                empty_program(EP),
                check_algebra_proof(EP, [comp(fit, [ST, FT])], EP, CE),
                if_commit(CE = left(CM), ( string_concat("proof rejected: ", CM, DM), die(DM) ), true),
                show_formula(F, FS),
                format("formula: ~w~n", [FS]),
                show_term_q(FT, FTS),
                format("term: ~w~n", [FTS]),
                length(Samples, LS),
                format("verified_on: ~d samples (~d held out), description length ~d~n", [LS, Held, Pen]),
                mnns_line(Fl, Samples),
                format("proof accepted: fit~n") ),
              ( format("no_formula~n"),
                mnns_line(Fl, Samples) )).
dispatch("program", [File, KeyS], Fl) :-
    program_cmd(Fl, File, KeyS).
dispatch("proof-check", [File, Out, ProofFile], _) :-
    load_program(File, Src),
    load_program(Out, Prog),
    read_text(ProofFile, PT),
    read_proof(PT, SE),
    if_commit(SE = right(Steps), true,
              ( SE = left(M0), format(string(DM0), "~w: ~w", [ProofFile, M0]), die(DM0) )),
    check_algebra_proof(Src, Steps, Prog, CE),
    if_commit(CE = right(Lines),
              print_lines(Lines),
              ( CE = left(M), string_concat("proof rejected: ", M, DM), die(DM) )).

print_lines([]).
print_lines([L|Ls]) :-
    format("~w~n", [L]),
    print_lines(Ls).

read_text(Path, Text) :-
    catch(read_file_to_string(Path, Text, [encoding(utf8)]), _,
          ( format(string(M), "~w: openFile: does not exist (No such file or directory)", [Path]), die(M) )).

load_program(Path, P) :-
    read_text(Path, Src),
    parse_program(Src, PE),
    if_commit(PE = right(P0), P = P0,
              ( PE = left(E), format(string(M), "~w: ~w", [Path, E]), die(M) )).

samples_t(Ss, T) :-
    findall(comp(s, [PL, int(V)]),
            ( member(Pos-V, Ss), findall(int(I), member(I, Pos), PIs), mk_list(PIs, atom('[]'), PL) ), Ts),
    mk_list(Ts, atom('[]'), T).

%  "2,4,8,16" or "[0,0]-1 [0,1]-2".
parse_samples(S, E) :-
    string_chars(S, Cs),
    if_commit(( memberchk('-', Cs), memberchk('[', Cs) ),
              ( split_string(S, " \t\n", " \t\n", Ws0),
                findall(W, ( member(W, Ws0), W \== "" ), Ws),
                catch(( maplist(pair_sample, Ws, Ps), E = right(Ps) ), bad_sample(M), E = left(M)) ),
              ( findall(C, ( member(C, Cs), if_commit(char_type(C, space), fail, true) ), Cs1),
                string_chars(S1, Cs1),
                split_string(S1, ",", "", Parts),
                maplist(read_int_or_die, Parts, Vs),
                numbered_list(Vs, 0, NVs),
                findall([I]-V, member(I-V, NVs), Ps),
                E = right(Ps) )).

pair_sample(W, Pos-V) :-
    if_commit(( once_det(sub_string(W, B, 1, _, "]")),
                sub_string(W, 0, 1, _, "["),
                B1 is B - 1,
                once_det(sub_string(W, 1, B1, _, PosS)),
                B2 is B + 1,
                once_det(sub_string(W, B2, 1, _, "-")),
                B3 is B + 2,
                once_det(sub_string(W, B3, _, 0, VS)),
                string_chars(VS, VCs),
                maplist(digit_or_minus, VCs) ),
              ( split_string(PosS, ",", "", PParts),
                maplist(read_int_or_die, PParts, Pos),
                read_int_or_die(VS, V) ),
              ( string_concat("bad sample ", W, M), throw(bad_sample(M)) )).

digit_or_minus(C) :-
    if_commit(char_type(C, digit(_)), true, C == '-').

read_int_or_die(S, N) :-
    if_commit(catch(number_string(N0, S), _, fail), N = N0, die("Prelude.read: no parse")).

%  mnns AlgebraPLOp's answer on the same values, for comparison.
mnns_line(Fl, Samples) :-
    fl_mnns(Fl, MM),
    if_commit(MM = just(D0), MD = just(D0),
              if_commit(getenv('MNNS_DIR', ED), MD = just(ED), MD = nothing)),
    if_commit(MD = just(D),
              if_commit(maplist(single_pos, Samples),
                        mnns_run(D, Samples),
                        format("mnns AlgebraPLOp: single-index samples only~n")),
              true).

single_pos([_]-_).

mnns_run(D, Samples) :-
    pairs_values(Samples, Vs),
    atomic_list_concat(Vs, ',', VA),
    format(atom(Goal), "use_module('~w/prolog/algebraplop/algebraplop'), mnn_algebraplop:infer_sequence_formula([~w], F), writeq(F), nl", [D, VA]),
    catch(( process_create(path(swipl), ['-q', '-g', Goal, '-t', halt],
                           [stdout(pipe(O)), stderr(pipe(Er)), process(Pid)]),
            read_string(O, _, OS), read_string(Er, _, _), close(O), close(Er),
            process_wait(Pid, Status) ),
          _, Status = failed),
    if_commit(Status == exit(0),
              ( split_string(OS, "\n", "", [L|_]), format("mnns AlgebraPLOp: ~w~n", [L]) ),
              format("mnns AlgebraPLOp: not available~n")).

% ---------------------------------------------------------------------------
% program

program_cmd(Fl, File, KeyS) :-
    load_program(File, Src),
    if_commit(once_det(sub_string(KeyS, B, 1, _, "/")),
              ( once_det(sub_string(KeyS, 0, B, _, FS)),
                B1 is B + 1,
                once_det(sub_string(KeyS, B1, _, 0, AS)),
                atom_string(P, FS),
                read_int_or_die(AS, N) ),
              die("expected NAME/2")),
    if_commit(N =:= 2, true, die("positions are read from a predicate NAME(Position, Value)")),
    Key = P/2,
    format(user_error, "MARK 0~n", []),
    extract_recurrence(Src, Key, MRec),
    format(user_error, "MARK 1~n", []),
    fl_domain(Fl, MD),
    if_commit(MD = just(Lo-Hi), true,
              if_commit(MRec = just(rec(RB, _, _, _)), ( Lo = RB, Hi is RB + 12 ), ( Lo = 0, Hi = 12 ))),
    sample_predicate(Src, Key, Lo, Hi, SE),
    if_commit(SE = right(Samples), true, ( SE = left(SM), die(SM) )),
    discover(Samples, MF),
    format(user_error, "MARK 2~n", []),
    if_commit(MF = just(found(F, _, _, _)), true,
              ( format("no_formula for ~w on ~d..~d~n", [KeyS, Lo, Hi]), throw(cli_exit(1)) )),
    if_commit(( MRec = just(Rec), induction_holds(Rec, F) ), Proved = true, Proved = false),
    if_commit(MRec = just(rec(RBase, _, _, _)), BaseLo = RBase, BaseLo = Lo),
    format(user_error, "MARK 3~n", []),
    if_commit(Proved == true,
              ( formula_clause(P, F, BaseLo, nothing, FormulaC),
                key_t(Key, KT), formula_term(F, FT), clause_t(FormulaC, FCT),
                EvidenceStep = comp(induction, [KT, FT, FCT]),
                Evidence = comp(proved, [atom(induction)]),
                DomainLo = BaseLo, DomainHi = nothing ),
              ( formula_clause(P, F, Lo, just(Hi), FormulaC),
                key_t(Key, KT), formula_term(F, FT), clause_t(FormulaC, FCT),
                EvidenceStep = comp(exhaustive, [KT, int(Lo), int(Hi), FT, FCT]),
                Evidence = comp(verified_on, [comp('..', [int(Lo), int(Hi)])]),
                DomainLo = Lo, DomainHi = just(Hi) )),
    if_commit(( F = poly(Terms), maplist(affine_term, Terms), coef(Terms, 1, A), A =\= 0 ),
              ( coef(Terms, 0, Bc),
                inverse_clause(P, A, Bc, DomainLo, DomainHi, InvC),
                clause_t(InvC, ICT),
                if_commit(DomainHi = just(DH), HT = int(DH), HT = atom(inf)),
                InverseCs = [InvC],
                InverseSteps = [comp(inverse, [KT, FT, int(DomainLo), HT, ICT])] ),
              ( InverseCs = [], InverseSteps = [] )),
    all_src_clauses(Src, AllSrc),
    format(user_error, "MARK 4~n", []),
    numbered_list(AllSrc, 1, NSrc),
    if_commit(Proved == true,
              findall(I-C1, ( member(I-C, NSrc), replace_loops(P, BaseLo, C, C1),
                              clause_t(C, CT0), clause_t(C1, CT1), not_teq(CT0, CT1) ), Loops),
              Loops = []),
    loop_clause(P, LoopC),
    format(user_error, "MARK 5~n", []),
    clause_t(LoopC, LCT),
    findall(comp(loop, [KT, int(I), C1T, LCT]), ( member(I-C1, Loops), clause_t(C1, C1T) ), LoopSteps),
    expr_term(F, [atom(i)], ExprT),
    RSpec = comp(r_spec, [KT, comp(position, [int(1)]), comp(value, [int(2)]),
                          comp(formula, [FT]), comp(expression, [ExprT]), Evidence]),
    concat_lists([[EvidenceStep], InverseSteps, LoopSteps, [RSpec]], Steps),
    format(user_error, "MARK 6~n", []),
    findall(C2, ( member(I-C, NSrc), if_commit(memberchk(I-CR, Loops), C2 = CR, C2 = C) ), OutSrc),
    if_commit(Loops == [], LoopCs = [], LoopCs = [LoopC]),
    max_var_id(RSpec, MV),
    RNV is MV + 1,
    concat_lists([OutSrc, [FormulaC], InverseCs, LoopCs, [clause(RSpec, atom(true), RNV)]], OutClauses),
    program_from_clauses(OutClauses, OutProg),
    format(user_error, "MARK 7~n", []),
    check_algebra_proof(Src, Steps, OutProg, CE),
    if_commit(CE = right(Report), true,
              ( CE = left(CM), string_concat("proof rejected: ", CM, DM), die(DM) )),
    show_formula(F, FS),
    format("formula: ~w at position i = ~w~n", [KeyS, FS]),
    show_term_q(Evidence, ES),
    if_commit(Proved == true, Note = "", Note = " (no first-order recurrence proof)"),
    format("evidence: ~w~w~n", [ES, Note]),
    if_commit(InverseCs = [_], format("inverse: ~w__inverse(V, N)~n", [P]), true),
    length(Loops, NL),
    if_commit(NL > 0,
              format("splice-index loops: ~d findall/between loop(s) replaced by ~w__loop/3~n", [NL, P]),
              true),
    mnns_line(Fl, Samples),
    print_lines(Report),
    show_program(OutProg, PS),
    format(string(H1), "% algebraplop2: positional formula for ~w, from ~w", [KeyS, File]),
    format(string(H2), "% ~w; the proof is in the .proof file.", [ES]),
    atomic_list_concat([H1, "\n", H2, "\n", "\n", PS], Text),
    fl_out(Fl, MO),
    if_commit(MO = just(O),
              ( write_file(O, Text),
                string_concat(O, ".proof", PO),
                proof_text(Steps, PTx),
                write_file(PO, PTx),
                format(user_error, "wrote ~w and ~w~n", [O, PO]) ),
              write(Text)).

write_file(Path, Text) :-
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]), write(S, Text), close(S)).

key_t(F/N, comp('/', [atom(F), int(N)])).

clause_t(clause(H, B, _), comp(':-', [H, B])).
