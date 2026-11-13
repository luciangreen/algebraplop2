/*  program.pl - positions from programs (port of the Haskell
    AlgebraPLOp2.Program): sampling a predicate p(I, V), and proving its
    formula by induction when p is a first-order recurrence.

    Data:
      rec(Base, BaseValue, A, G)     p(B, VB).
                                     p(N, V) :- N > B, N1 is N - 1, p(N1, V1),
                                                V is A * V1 + G(N).
      G is a polynomial in N: its coefficients of N^0, N^1, ...
*/

teq(A, B) :-
    same_term(A, B, true).

poly_eval(Cs, X, V) :-
    rev(Cs, R),
    foldl(horner(X), R, 0, V).

horner(X, C, Acc, V) :-
    V is C + X * Acc.

%  extract_recurrence(+Prog, +Key, -Maybe): a first-order recurrence in the
%  source clauses of p/2 (in either clause order).
extract_recurrence(Prog, Key, M) :-
    if_commit(( Key = F/2, prog_lookup(Prog, Key, just([C1, C2])) ),
              if_commit(( base_of(C1, B, VB), step_of(F, C2, B1, A, G), B =:= B1 ),
                        M = just(rec(B, VB, A, G)),
                        if_commit(( base_of(C2, B, VB), step_of(F, C1, B1, A, G), B =:= B1 ),
                                  M = just(rec(B, VB, A, G)),
                                  M = nothing)),
              M = nothing).

base_of(clause(H, Body, _), B, VB) :-
    H = comp(_, [int(B), int(VB)]),
    Body == atom(true).

step_of(F, clause(H, Body, _), B, A, G) :-
    H = comp(_, [N, V]),
    N = var(_, _),
    V = var(_, _),
    conj_list(Body, Gs),
    Gs = [comp('>', [N1, int(B)]),
          comp(is, [NM1, comp('-', [N2, int(1)])]),
          comp(G0, [NM1b, V1]),
          comp(is, [V2, E])],
    NM1 = var(_, _),
    V1 = var(_, _),
    teq(N1, N), teq(N2, N), teq(NM1b, NM1), G0 == F, teq(V2, V),
    if_commit(teq(V1, V), fail, true),
    if_commit(teq(NM1, N), fail, true),
    linear_in(V1, N, NM1, E, just(A-G)).

%  E as A * V1 + G(N), where N1 stands for N - 1.  A polynomial in V1 is a
%  list of Degree-PolyN pairs.
linear_in(V1, N, N1, E, M) :-
    if_commit(lpoly(V1, N, N1, E, P),
              ( lp_get(P, 0, Deg0),
                lp_get(P, 1, Deg1),
                if_commit(( member(D-Cs, P), D > 1, member(C, Cs), C =\= 0 ),
                          M = nothing,
                          ( trim_zeros(Deg1, T1),
                            trim_zeros(Deg0, T0),
                            if_commit(T1 == [], M = just(0-T0),
                                      if_commit(T1 = [A], M = just(A-T0), M = nothing)) )) ),
              M = nothing).

lp_get(P, D, Cs) :-
    if_commit(memberchk(D-Cs0, P), Cs = Cs0, Cs = []).

trim_zeros(Cs, T) :-
    rev(Cs, R),
    drop_zeros(R, R1),
    rev(R1, T).

drop_zeros([], []).
drop_zeros([X|Xs], Out) :-
    if_commit(X =:= 0, drop_zeros(Xs, Out), Out = [X|Xs]).

lpoly(V1, N, N1, T, P) :-
    if_commit(T = int(I), P = [0-[I]],
    if_commit(teq(T, V1), P = [1-[1]],
    if_commit(teq(T, N), P = [0-[0, 1]],
    if_commit(teq(T, N1), P = [0-[-1, 1]],
    if_commit(T = comp('+', [A, B]),
              ( lpoly(V1, N, N1, A, PA), lpoly(V1, N, N1, B, PB), add_p(PA, PB, P) ),
    if_commit(T = comp('-', [A, B]),
              ( lpoly(V1, N, N1, A, PA), lpoly(V1, N, N1, B, PB), neg_p(PB, NB), add_p(PA, NB, P) ),
    if_commit(T = comp('-', [A]),
              ( lpoly(V1, N, N1, A, PA), neg_p(PA, P) ),
    if_commit(T = comp('*', [A, B]),
              ( lpoly(V1, N, N1, A, PA), lpoly(V1, N, N1, B, PB), mul_p(PA, PB, P) ),
    if_commit(( T = comp(Op, [A, int(K)]), memberchk(Op, ['^', '**']), K >= 0, K =< 6 ),
              ( lpoly(V1, N, N1, A, PA), pow_p(PA, K, P) ),
              fail))))))))).

pow_p(PA, K, P) :-
    if_commit(K =:= 0, P = [0-[1]], ( K1 is K - 1, pow_p(PA, K1, P0), mul_p(PA, P0, P) )).

%  maps from degree to coefficient lists, kept sorted by degree
add_p(PA, PB, P) :-
    conc(PA, PB, All),
    combine(All, P).

combine(Pairs, P) :-
    pairs_keys(Pairs, Ks0),
    sort(Ks0, Ks),
    findall(K-Cs, ( member(K, Ks), findall(C0, member(K-C0, Pairs), CL), foldl(pn_add, CL, [], Cs) ), P).

neg_p(PA, P) :-
    findall(K-Ns, ( member(K-Cs, PA), maplist(neg_n, Cs, Ns) ), P).

neg_n(X, Y) :-
    Y is -X.

mul_p(PA, PB, P) :-
    findall(K-C, ( member(I-A, PA), member(J-B, PB), K is I + J, mul_n(A, B, C) ), Pairs),
    combine(Pairs, P).

pn_add(A, B, C) :-
    length(A, LA),
    length(B, LB),
    L is max(LA, LB),
    pad_zeros(A, L, A1),
    pad_zeros(B, L, B1),
    maplist(sum2, A1, B1, C).

sum2(X, Y, Z) :-
    Z is X + Y.

pad_zeros(Xs, L, Ys) :-
    length(Xs, LX),
    K is L - LX,
    findall(0, between(1, K, _), Zs),
    conc(Xs, Zs, Ys).

mul_n(A, B, C) :-
    length(A, LA),
    length(B, LB),
    Top is LA + LB - 2,
    findall(S, ( between(0, Top, K),
                 findall(X, ( between(0, K, I), I < LA, KI is K - I, KI < LB,
                              I1 is I + 1, KI1 is KI + 1,
                              nth_det(I1, A, just(AI)), nth_det(KI1, B, just(BK)),
                              X is AI * BK ), Xs),
                 sum_list(Xs, S) ), C).

%  induction_holds(+Rec, +Formula): f(B) = VB, and f(n) = A f(n-1) + G(n)
%  for all n.  For a polynomial f the difference is a polynomial of degree
%  at most D, so it is zero when it is zero at D + 1 points; for
%  a b^n + c it is checked symbolically.
induction_holds(rec(B, VB, A, G), F) :-
    eval_f(F, [B], FB),
    FB =:= VB,
    step_holds(F, B, A, G).

step_holds(F, B, A, G) :-
    if_commit(( F = poly(Terms), maplist(single_index, Terms) ),
              ( findall(E, member([E]-_, Terms), Es),
                length(G, LG),
                max_list([0, LG|Es], M0),
                D is M0 + 1,
                D1 is D + 1,
                findall(P, ( between(0, D1, K), P is B + 1 + K ), Pts),
                maplist(step_at(F, A, G), Pts) ),
              if_commit(F = geo(AA, BB, C),
                        ( if_commit(AA =:= 0, true, BB =:= A),
                          drop(1, G, GT), all_zero(GT),
                          if_commit(G = [G0|_], true, G0 = 0),
                          G0 =:= C * (1 - A) ),
                        fail)).

single_index(Es-_) :-
    Es = [_].

step_at(F, A, G, P) :-
    eval_f(F, [P], FP),
    P1 is P - 1,
    eval_f(F, [P1], FP1),
    poly_eval(G, P, GP),
    FP =:= A * FP1 + GP.

%  sample_predicate(+Prog, +Key, +Lo, +Hi, -Either): values p(I, V) for I in
%  Lo..Hi (first answer each), on the cutless interpreter.
sample_predicate(Prog, F/_, Lo, Hi, E) :-
    with_prelude(Prog, P),
    sample_go(Lo, Hi, P, F, [], E).

sample_go(I, Hi, P, F, Acc, E) :-
    if_commit(I > Hi,
              ( rev(Acc, Ss), E = right(Ss) ),
              ( default_options(Opts),
                run_goal(Opts, P, comp(F, [int(I), var(0, 'V')]), 1, S),
                head_answer(S, _, R),
                sample_one(R, I, E1),
                if_commit(E1 = right(Sm),
                          ( I1 is I + 1, sample_go(I1, Hi, P, F, [Sm|Acc], E) ),
                          E = E1) )).

sample_one(first(St), I, E) :-
    resolve(var(0, 'V'), St, T),
    if_commit(T = int(V), E = right([I]-V),
              ( haskell_show_term(T, TS),
                format(string(M), "p(~d, V) gave a non-integer ~w", [I, TS]),
                E = left(M) )).
sample_one(stop(Msg), I, left(M)) :-
    format(string(M), "p(~d, V): ~w", [I, Msg]).
sample_one(none, I, left(M)) :-
    format(string(M), "p(~d, V) failed", [I]).

%  Haskell's derived show of a term.
haskell_show_term(T, S) :-
    if_commit(T = var(I, N), ( hs_str(N, NS), format(string(S), "Var ~w ~w", [I, NS]) ),
    if_commit(T = atom(A), ( hs_str(A, AS), format(string(S), "Atom ~w", [AS]) ),
    if_commit(T = int(I), ( hs_int(I, IS), format(string(S), "Int ~w", [IS]) ),
    if_commit(T = flt(D), ( show_float(D, DS0), hs_neg(D, DS0, DS), format(string(S), "Flt ~w", [DS]) ),
              ( T = comp(F, As), hs_str(F, FS), maplist(haskell_show_term, As, ASs),
                atomic_list_concat(ASs, ',', AL),
                format(string(S), "Comp ~w [~w]", [FS, AL]) ))))).

hs_str(A, S) :-
    atom_string(A, AS),
    with_output_to(string(S), writeq(AS)).

hs_int(I, S) :-
    if_commit(I < 0, format(string(S), "(~d)", [I]), format(string(S), "~d", [I])).

hs_neg(D, DS0, DS) :-
    if_commit(D < 0, format(string(DS), "(~w)", [DS0]), DS = DS0).
