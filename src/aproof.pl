/*  aproof.pl - the independent checker for algebraplop2 proofs (port of
    the Haskell AlgebraPLOp2.Proof).

    Steps (Prolog terms, one per rewrite):

      fit(Samples, Formula)                      verified_on: reproduces every
                                                 sample, with at least one
                                                 held-out sample
      induction(P/2, Formula, Clause)            proved: base case and step
                                                 identity, read off the source
                                                 by evaluation
      exhaustive(P/2, Lo, Hi, Formula, Clause)   verified_on(Lo..Hi): the source
                                                 is run on every position
      inverse(P/2, Formula, Lo, Hi, Clause)      the inverse of an affine formula
      loop(P/2, ClauseIndex, NewClause, LoopClause)
                                                 a splice-index loop replacing
                                                 findall/3 over between/3
      r_spec(...)                                provenance facts

    The checker does not use the discovery code: it evaluates the source's
    own arithmetic (with detlog2's evaluator) to read the recurrence, and
    runs the source to compare values.  A failed condition is thrown as
    ap_fail(Message).
*/

ap_ensure(G, Msg) :-
    if_commit(G, true, throw(ap_fail(Msg))).

ap_fail(Msg) :-
    throw(ap_fail(Msg)).

proof_text(Steps, Text) :-
    findall(L, ( member(S, Steps), show_term_q(S, T), format(string(L), "~w.\n", [T]) ), Ls),
    atomic_list_concat(["% algebraplop2 proof: one step per rewrite (see docs/proof_rules.md).\n"|Ls], A),
    atom_string(A, Text).

read_proof(Src, E) :-
    parse_program(Src, PE),
    if_commit(PE = right(P),
              ( program_clauses(P, KCs),
                findall(T, ( member(_-Cs, KCs), member(C, Cs), clause_term(C, T) ), Steps),
                E = right(Steps) ),
              E = PE).

% ---------------------------------------------------------------------------
% Templates (shared with the generator; they are checked against the source
% by evaluation below)

%  P__formula(N, V) :- integer(N), N >= Lo [, N =< Hi], V is Expr.
formula_clause(P, F, Lo, MHi, clause(comp(Name, [N, V]), Body, 2)) :-
    atom_concat(P, '__formula', Name),
    N = var(0, 'N'),
    V = var(1, 'V'),
    if_commit(MHi = just(Hi), HG = [comp('=<', [N, int(Hi)])], HG = []),
    expr_term(F, [N], E),
    concat_lists([[comp(integer, [N]), comp('>=', [N, int(Lo)])], HG, [comp(is, [V, E])]], Gs),
    mk_conj(Gs, Body).

%  P__inverse(V, N) for an affine formula a*N + b with integer a /= 0.
inverse_clause(P, A, B, Lo, MHi, clause(comp(Name, [V, N]), Body, 3)) :-
    atom_concat(P, '__inverse', Name),
    V = var(0, 'V'),
    N = var(1, 'N'),
    D = var(2, 'D'),
    if_commit(MHi = just(Hi), HG = [comp('=<', [N, int(Hi)])], HG = []),
    conc([comp(integer, [V]), comp(is, [D, comp('-', [V, int(B)])]),
          comp('=:=', [comp(mod, [D, int(A)]), int(0)]), comp(is, [N, comp('//', [D, int(A)])]),
          comp('>=', [N, int(Lo)])], HG, Gs),
    mk_conj(Gs, Body).

%  P__loop(I, H, Vs): the values at positions I..H, by the formula.
loop_clause(P, clause(comp(LN, [I, H, Vs]), Body, 6)) :-
    atom_concat(P, '__loop', LN),
    atom_concat(P, '__formula', FN),
    I = var(0, 'I'),
    H = var(1, 'H'),
    Vs = var(2, 'Vs'),
    V = var(3, 'V'),
    I1 = var(4, 'I1'),
    Vs1 = var(5, 'Vs1'),
    mk_conj([comp(FN, [I, V]), comp(is, [I1, comp('+', [I, int(1)])]),
             comp('=', [Vs, comp('.', [V, Vs1])]), comp(LN, [I1, H, Vs1])], Rec),
    Body = comp(';', [comp('->', [comp('>', [I, H]), comp('=', [Vs, atom('[]')])]), Rec]).

%  The goal replacing findall(V, (between(L, H, I), p(I, V)), Vs).
loop_goal(P, Base, L, H, Vs, Original, G) :-
    atom_concat(P, '__loop', LN),
    mk_conj([comp(integer, [L]), comp(integer, [H]), comp('>=', [L, int(Base)])], Cond),
    G = comp(';', [comp('->', [Cond, comp(LN, [L, H, Vs])]), Original]).

%  Replace findall(V, (between(L, H, I), p(I, V)), Vs) goals in a clause.
replace_loops(P, Base, clause(H, B, NV), clause(H, B1, NV)) :-
    replace_loops_t(P, Base, B, B1).

replace_loops_t(P, Base, T, T1) :-
    if_commit(( T = comp(findall, [V, comp(',', [comp(between, [L, HH, I]), comp(Q, [I1, V1])]), Vs]),
                Q == P, teq(I, I1), teq(V, V1), I = var(_, _), V = var(_, _) ),
              loop_goal(P, Base, L, HH, Vs, T, T1),
              if_commit(( T = comp(Op, [X, Y]), memberchk(Op, [',', ';', '->']) ),
                        ( replace_loops_t(P, Base, X, X1), replace_loops_t(P, Base, Y, Y1),
                          T1 = comp(Op, [X1, Y1]) ),
                        T1 = T)).

% ---------------------------------------------------------------------------
% Checking

ap_variant(A, B) :-
    clause_term(A, TA),
    clause_term(B, TB),
    empty_state(0, St),
    variant_t(St, TA, TB, true).

ap_show_key(F/N, S) :-
    format(string(S), "~w/~d", [F, N]).

all_src_clauses(Src, Cls) :-
    program_clauses(Src, KCs),
    findall(C, ( member(_-Cs, KCs), member(C, Cs) ), Cls).

%  check_algebra_proof(+Source, +Steps, +Out, -Either)
check_algebra_proof(Src, Steps, Out, E) :-
    catch(( check_algebra_proof_(Src, Steps, Out, R), E = right(R) ),
          ap_fail(M),
          E = left(M)).

check_algebra_proof_(Src, Steps, Out, [Report]) :-
    maplist(proved_step(Src), Steps, ProvedL),
    concat_lists(ProvedL, Proved),
    maplist(justified_step(Src, Steps, Out, Proved), Steps, JL),
    concat_lists(JL, Justified),
    findall(CI, member(comp(loop, [_, int(CI), _, _]), Steps), ReplacedIdx),
    all_src_clauses(Src, AllSrc),
    numbered_list(AllSrc, 1, NSrc),
    findall(C, ( member(I-C, NSrc), not_memberchk(I, ReplacedIdx) ), SrcCls),
    findall(clause(S, atom(true), NV),
            ( member(S, Steps), S = comp(r_spec, _), max_var_id(S, MV), NV is MV + 1 ), RSpecs),
    uniq_clauses(Justified, UJ),
    concat_lists([SrcCls, UJ, RSpecs], Expected),
    all_src_clauses(Out, OutCls),
    length(OutCls, LO),
    length(Expected, LE),
    format(string(M1), "the output has ~d clauses, the proof justifies ~d", [LO, LE]),
    ap_ensure(LO =:= LE, M1),
    maplist(out_justified(Expected), OutCls),
    length(Steps, LS),
    format(string(Report), "proof accepted: ~d steps", [LS]).

not_memberchk(X, L) :-
    if_commit(memberchk(X, L), fail, true).

out_justified(Expected, C) :-
    clause_term(C, T),
    show_term_q(T, TS),
    string_concat("unjustified clause: ", TS, M),
    ap_ensure(( member(E, Expected), ap_variant(C, E) ), M).

uniq_clauses([], []).
uniq_clauses([C|Cs], [C|U]) :-
    findall(D, ( member(D, Cs), if_commit(ap_variant(C, D), fail, true) ), Rest),
    uniq_clauses(Rest, U).

proved_step(Src, S, Out) :-
    if_commit(S = comp(induction, [KT, FT, ClT]),
              ( key_of(KT, Key),
                formula_of(FT, F),
                ap_as_clause(ClT, Cl),
                check_induction(Src, Key, F, Base),
                Key = P/_,
                formula_clause(P, F, Base, nothing, Want),
                ap_show_key(Key, KS),
                string_concat(KS, ": the formula clause is not the template", M),
                ap_ensure(ap_variant(Cl, Want), M),
                B12 is Base + 12,
                sample_agree(Src, Key, Cl, Base, B12),
                Out = [Key-Base] ),
              Out = []).

justified_step(Src, Steps, OutP, Proved, S, Out) :-
    if_commit(step_shape(S, Name),
              step_check(Name, S, Src, Steps, OutP, Proved, Out),
              ( show_term_q(S, ST), take_chars(80, ST, ST80),
                string_concat("unknown step ", ST80, M), ap_fail(M) )).

step_shape(S, Name) :-
    if_commit(S = comp(fit, [_, _]), Name = fit,
    if_commit(S = comp(induction, [_, _, _]), Name = induction,
    if_commit(S = comp(exhaustive, [_, int(_), int(_), _, _]), Name = exhaustive,
    if_commit(S = comp(inverse, [_, _, int(_), _, _]), Name = inverse,
    if_commit(S = comp(loop, [_, int(_), _, _]), Name = loop,
    if_commit(S = comp(r_spec, _), Name = r_spec,
              fail)))))).

take_chars(N, S, T) :-
    string_chars(S, Cs),
    take(N, Cs, Cs1),
    string_chars(T, Cs1).

step_check(fit, comp(fit, [SamplesT, FT]), _, _, _, _, []) :-
    formula_of(FT, F),
    samples_of(SamplesT, Samples),
    ap_ensure(fits_all(F, Samples), "fit: the formula does not reproduce every sample"),
    length(Samples, L),
    params(F, NP),
    ap_ensure(L > NP, "fit: no held-out sample (more parameters than samples allow)").
step_check(induction, comp(induction, [_, _, ClT]), _, _, _, _, [Cl]) :-
    ap_as_clause(ClT, Cl).
step_check(exhaustive, comp(exhaustive, [KT, int(Lo), int(Hi), FT, ClT]), Src, _, _, _, [Cl]) :-
    key_of(KT, Key),
    formula_of(FT, F),
    ap_as_clause(ClT, Cl),
    Key = P/_,
    formula_clause(P, F, Lo, just(Hi), Want),
    ap_show_key(Key, KS),
    string_concat(KS, ": the formula clause is not the template", M),
    ap_ensure(ap_variant(Cl, Want), M),
    exhaustive_go(Lo, Hi, Src, Key, KS, F),
    sample_agree(Src, Key, Cl, Lo, Hi).
step_check(inverse, comp(inverse, [KT, FT, int(Lo), HiT, ClT]), _, Steps, OutP, Proved, [Cl]) :-
    key_of(KT, Key),
    formula_of(FT, F),
    ap_as_clause(ClT, Cl),
    if_commit(HiT = int(Hi0), MHi = just(Hi0), MHi = nothing),
    if_commit(( F = poly(Terms), maplist(affine_term, Terms) ),
              ( coef(Terms, 1, A), coef(Terms, 0, B) ),
              ap_fail("inverse: only integer affine formulas are inverted")),
    ap_ensure(A =\= 0, "inverse: constant formula"),
    Key = P/_,
    inverse_clause(P, A, B, Lo, MHi, Want),
    ap_ensure(ap_variant(Cl, Want), "inverse: template"),
    ap_ensure(if_commit(memberchk(Key-_, Proved), true,
                        ( member(St, Steps), covers_range(Key, Lo, MHi, St) )),
              "inverse: the formula is not proved on this range"),
    if_commit(MHi = just(Hi), true, Hi is Lo + 20),
    with_prelude(OutP, Prog),
    atom_concat(P, '__inverse', IN),
    inverse_go(Lo, Hi, A, B, IN, Prog).
step_check(loop, comp(loop, [KT, int(CI), NewT, LoopT]), Src, _, _, Proved, [NewC, LoopC]) :-
    key_of(KT, Key),
    Key = P/_,
    ap_show_key(Key, KS),
    if_commit(memberchk(Key-Base, Proved), true,
              ( format(string(M0), "loop: ~w has no induction proof", [KS]), ap_fail(M0) )),
    ap_as_clause(NewT, NewC),
    ap_as_clause(LoopT, LoopC),
    loop_clause(P, WantLoop),
    ap_ensure(ap_variant(LoopC, WantLoop), "loop: loop template"),
    all_src_clauses(Src, AllSrc),
    length(AllSrc, LA),
    ap_ensure(( CI >= 1, CI =< LA ), "loop: no such clause"),
    nth_det(CI, AllSrc, just(Old)),
    replace_loops(P, Base, Old, WantNew),
    ap_ensure(ap_variant(NewC, WantNew), "loop: the new clause is not the source clause with its loops replaced").
step_check(r_spec, _, _, _, _, _, []).

affine_term(Es-C) :-
    Es = [E],
    E =< 1,
    rat_den(C, D),
    D =:= 1.

coef(Terms, E, Sum) :-
    findall(N, ( member([E1]-C, Terms), E1 =:= E, rat_num(C, N) ), Ns),
    sum_list(Ns, Sum).

covers_range(Key, Lo, MHi, St) :-
    St = comp(exhaustive, [KT, int(L), int(H), _, _]),
    key_of_m(KT, just(Key1)),
    Key1 == Key,
    L =< Lo,
    MHi = just(Hi),
    Hi =< H.

inverse_go(N, Hi, A, B, IN, Prog) :-
    if_commit(N > Hi, true,
              ( Val is A * N + B,
                first_of_ap(Prog, comp(IN, [int(Val), var(0, 'N')]), var(0, 'N'), R),
                format(string(M), "inverse: ~d does not give ~d", [Val, N]),
                ap_ensure(R == just(int(N)), M),
                N1 is N + 1,
                inverse_go(N1, Hi, A, B, IN, Prog) )).

exhaustive_go(I, Hi, Src, Key, KS, F) :-
    if_commit(I > Hi, true,
              ( run_source(Src, Key, I, V),
                eval_f(F, [I], X),
                format(string(M), "~w: the formula differs from the program at ~d", [KS, I]),
                ap_ensure(( V = just(VV), VV =:= X ), M),
                I1 is I + 1,
                exhaustive_go(I1, Hi, Src, Key, KS, F) )).

sample_agree(Src, Key, Cl, Lo, Hi) :-
    all_src_clauses(Src, AllSrc),
    program_from_clauses([Cl|AllSrc], P0),
    with_prelude(P0, Prog),
    Key = P/_,
    atom_concat(P, '__formula', FN),
    ap_show_key(Key, KS),
    sample_agree_go(Lo, Hi, Src, Key, KS, FN, Prog).

sample_agree_go(I, Hi, Src, Key, KS, FN, Prog) :-
    if_commit(I > Hi, true,
              ( run_source(Src, Key, I, V),
                first_of_ap(Prog, comp(FN, [int(I), var(0, 'V')]), var(0, 'V'), R),
                if_commit(( V = just(VV), rat_den(VV, 1) ), ( rat_num(VV, VN), W = just(int(VN)) ), W = nothing),
                format(string(M), "~w: the emitted clause differs from the program at ~d", [KS, I]),
                ap_ensure(same_maybe(W, R), M),
                I1 is I + 1,
                sample_agree_go(I1, Hi, Src, Key, KS, FN, Prog) )).

same_maybe(A, B) :-
    if_commit(A == nothing, B == nothing,
              ( A = just(X), B = just(Y), teq(X, Y) )).

%  run_source(+Src, +Key, +I, -MaybeValue): the source's first answer for
%  p(I, V), with ordinary cut semantics.
run_source(Src, P/_, I, M) :-
    with_prelude(Src, Prog),
    default_options(Opts),
    ref_run(Opts, Prog, comp(P, [int(I), var(0, 'V')]), 10, S),
    head_answer(S, _, R),
    if_commit(R = stop(E), ap_fail(E), true),
    if_commit(( R = first(St), resolve(var(0, 'V'), St, int(V)) ), M = just(V), M = nothing).

first_of_ap(Prog, G, V, M) :-
    default_options(Opts),
    run_goal(Opts, Prog, G, 10, S),
    head_answer(S, _, R),
    if_commit(R = stop(E), ap_fail(E), true),
    if_commit(R = first(St), ( resolve(V, St, T), M = just(T) ), M = nothing).

key_of(T, K) :-
    key_of_m(T, M),
    if_commit(M = just(K0), K = K0,
              ( show_term_q(T, S), string_concat("bad predicate indicator ", S, Msg), ap_fail(Msg) )).

key_of_m(T, M) :-
    if_commit(T = comp('/', [atom(F), int(N)]), M = just(F/N), M = nothing).

formula_of(T, F) :-
    formula_from_term(T, M),
    if_commit(M = just(F0), F = F0,
              ( show_term_q(T, S), string_concat("bad formula ", S, Msg), ap_fail(Msg) )).

samples_of(T, Ss) :-
    ap_list_of(T, L),
    maplist(sample_of, L, Ss).

sample_of(X, Pos-V) :-
    if_commit(X = comp(s, [PosT, int(V0)]),
              ( ap_list_of(PosT, Ps), maplist(pos_int, Ps, Pos), V = V0 ),
              ( show_term_q(X, S), string_concat("bad sample ", S, M), ap_fail(M) )).

pos_int(X, I) :-
    if_commit(X = int(I0), I = I0, ap_fail("bad position")).

ap_list_of(T, L) :-
    if_commit(T == atom('[]'), L = [],
              if_commit(T = comp('.', [H, Tl]),
                        ( ap_list_of(Tl, L0), L = [H|L0] ),
                        ( show_term_q(T, S), string_concat("not a list: ", S, Msg), ap_fail(Msg) ))).

ap_as_clause(T, C) :-
    max_var_id(T, MV),
    NV is MV + 1,
    if_commit(T = comp(':-', [H, B]),
              C = clause(H, B, NV),
              if_commit(is_callable_t(T, true),
                        C = clause(T, atom(true), NV),
                        ( show_term_q(T, S), string_concat("not a clause: ", S, M), ap_fail(M) ))).

params(poly(Terms), N) :-
    if_commit(Terms = [Es-_|_], length(Es, M), M = 1),
    findall(S, ( member(E-_, Terms), sum_list(E, S) ), Ss),
    max_list([0|Ss], D),
    vectors(M, D, Vs),
    findall(V, ( member(V, Vs), sum_list(V, S), S =< D ), Ok),
    length(Ok, N).
params(geo(_, _, _), 3).
params(periodic(_, Fs), N) :-
    maplist(params, Fs, Ns),
    sum_list(Ns, N).

% ---------------------------------------------------------------------------
% Induction: base case and step identity, read from the source by
% evaluating its own arithmetic.

check_induction(Src, Key, F, Base) :-
    Key = P/_,
    ap_show_key(Key, KS),
    format(string(Here), "induction for ~w: ", [KS]),
    prog_lookup(Src, Key, MCls),
    maybe_default(MCls, [], Cls),
    if_commit(( Cls = [C1, C2], base_of(C1, B0, VB0) ), ( Base = B0, VB = VB0, Step = C2 ),
    if_commit(( Cls = [C1, C2], base_of(C2, B0, VB0) ), ( Base = B0, VB = VB0, Step = C1 ),
              ( string_concat(Here, "expected a base clause p(B, V) and one recursive clause", M0), ap_fail(M0) ))),
    if_commit(( Step = clause(H, Body, _), H = comp(_, [NT, VT]), NT = var(_, _), VT = var(_, _) ), true,
              ( string_concat(Here, "the recursive clause head", M1), ap_fail(M1) )),
    conj_list(Body, Gs),
    if_commit(( Gs = [comp('>', [N1, int(B1)]), comp(is, [N1T, comp('-', [N2, int(1)])]),
                      comp(Q, [N1Tb, V1T]), comp(is, [V2, E])],
                N1T = var(_, _), V1T = var(_, _),
                teq(N1, NT), teq(N2, NT), teq(N1Tb, N1T), Q == P, teq(V2, VT), B1 =:= Base,
                not_teq(V1T, VT), not_teq(N1T, NT), not_teq(V1T, NT) ),
              true,
              ( string_concat(Here, "the recursive clause is not N > B, N1 is N - 1, p(N1, V1), V is E", M2), ap_fail(M2) )),
    eval_f(F, [Base], FB),
    string_concat(Here, "base case", M3),
    ap_ensure(FB =:= VB, M3),
    string_concat(Here, "E uses other variables", M4),
    ap_ensure(only_vars([NT, N1T, V1T], E), M4),
    if_commit(F = poly(Terms),
              ( findall(S, ( member(Es-_, Terms), sum_list(Es, S) ), Ss), max_list([0|Ss], DV) ),
              DV = 0),
    degree_of(E, DV, Deg),
    Deg2 is Deg + 2,
    findall(Pt, ( between(0, Deg2, K), Pt is Base + 1 + K ), Pts),
    Ctx = ev(NT, N1T, V1T, E),
    maplist(a_value(Here, Ctx), Pts, AVals),
    AVals = [A-_|_],
    string_concat(Here, "the coefficient of V1 depends on N", M5),
    ap_ensure(maplist(same_a(A), AVals), M5),
    if_commit(F = poly(_),
              maplist(poly_step(Here, Ctx, F), Pts),
              if_commit(F = geo(AA, BB, C),
                        ( string_concat(Here, "G is not c (1 - A)", M6),
                          ap_ensure(maplist(g_is(C, A), AVals), M6),
                          string_concat(Here, "the base of the power is not A", M7),
                          ap_ensure(if_commit(AA =:= 0, true, BB =:= A), M7) ),
                        ( string_concat(Here, "only polynomial and a*b^n+c formulas are proved by induction", M8),
                          ap_fail(M8) ))).

not_teq(A, B) :-
    if_commit(teq(A, B), fail, true).

only_vars(Vs, T) :-
    findall(I, member(var(I, _), Vs), Ids),
    term_vars_ordered(T, TVs),
    if_commit(( member(var(J, _), TVs), not_memberchk(J, Ids) ), fail, true).

same_a(A, X-_) :-
    X =:= A.

g_is(C, A, _-G) :-
    G =:= C * (1 - A).

%  E evaluated at V1 = X and N = Nv
eval_e(ev(NT, N1T, V1T, E), X, Nv, R) :-
    empty_state(100000, St0),
    Nm1 is Nv - 1,
    foldl(bind_one, [NT-int(Nv), N1T-int(Nm1), V1T-X], St0, St),
    eval_arith(St, E, R0),
    if_commit(R0 = right(ni(I)), R = I,
              if_commit(R0 = right(nf(D)), R is rational(D),
                        ( R0 = left(Err), ap_fail(Err) ))).

bind_one(V-T, St0, St) :-
    unify(V, T, St0, M),
    maybe_default(M, St0, St).

a_value(Here, Ctx, Nv, A-E0) :-
    eval_e(Ctx, int(0), Nv, E0),
    eval_e(Ctx, int(1), Nv, E1),
    eval_e(Ctx, int(2), Nv, E2),
    string_concat(Here, "E is not linear in V1", M),
    ap_ensure(E2 - E0 =:= 2 * (E1 - E0), M),
    A is E1 - E0.

poly_step(Here, Ctx, F, Nv) :-
    Nm1 is Nv - 1,
    eval_f(F, [Nm1], Prev),
    rat_t(Prev, PT),
    eval_e(Ctx, PT, Nv, En),
    eval_f(F, [Nv], FN),
    format(string(M), "~wstep identity fails at ~d", [Here, Nv]),
    ap_ensure(FN =:= En, M).

%  a bound on the degree in N, with V1 of degree DV
degree_of(T, DV, D) :-
    if_commit(T = int(_), D = 0,
    if_commit(T = var(_, _), D is max(1, DV),
    if_commit(( T = comp(Op, [X, Y]), memberchk(Op, ['+', '-']) ),
              ( degree_of(X, DV, DX), degree_of(Y, DV, DY), D is max(DX, DY) ),
    if_commit(T = comp('*', [X, Y]),
              ( degree_of(X, DV, DX), degree_of(Y, DV, DY), D is DX + DY ),
    if_commit(( T = comp(Op, [X, int(K)]), memberchk(Op, ['^', '**']) ),
              ( degree_of(X, DV, DX), D is K * DX ),
    if_commit(T = comp('-', [X]), degree_of(X, DV, D),
              D = 100)))))).
