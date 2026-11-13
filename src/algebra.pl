/*  algebra.pl - positional formulas with exact rational arithmetic (port of
    the Haskell AlgebraPLOp2.Algebra).

    A position is a list of integer indices (one index for a sequence,
    several for a table).  Candidate formulas are fitted exactly (Gaussian
    elimination over the rationals), must reproduce held-out samples they
    were not fitted on, and are ranked by a description-length penalty, so
    the result is deterministic: one answer.

    Data:
      Pos-Value                      a sample
      poly([Es-C, ...])              sum of C * product of index^exponent
      geo(A, B, C)                   A * B^i + C (one index)
      periodic(P, [F, ...])          formula (i mod P), applied to i
      found(F, Fitted, HeldOut, Penalty)

    Numbers are SWI-Prolog integers and rationals (rdiv), which are exact.
*/

% ---------------------------------------------------------------------------
% Rationals

rat_num(R, N) :-
    rational(R, N, _).

rat_den(R, D) :-
    rational(R, _, D).

%  rat_pow(+Base, +Exp, -R): Base^Exp for an integer exponent (Haskell ^^).
rat_pow(B, E, R) :-
    if_commit(E >= 0, R is B ^ E, ( E1 is -E, P is B ^ E1, R is 1 rdiv P )).

last_of(L, X) :-
    rev(L, [X|_]).

lcm_i(A, B, L) :-
    G is gcd(A, B),
    L is abs(A * B) // G.

% ---------------------------------------------------------------------------
% Evaluation

%  eval_f(+Formula, +Pos, -Value)
eval_f(poly(Terms), Pos, V) :-
    foldl(poly_term_acc(Pos), Terms, 0, V).
eval_f(geo(A, B, C), Pos, V) :-
    if_commit(Pos = [I],
              if_commit(I >= 0,
                        V is A * B ^ I + C,
                        ( I1 is -I, P is B ^ I1, V is A rdiv P + C )),
              V = 0).
eval_f(periodic(P, Fs), Pos, V) :-
    if_commit(Pos = [I],
              ( Ix is I mod P, Ix1 is Ix + 1, nth_det(Ix1, Fs, just(F)), eval_f(F, Pos, V) ),
              V = 0).

poly_term_acc(Pos, Es-C, A0, A) :-
    mono_value(Pos, Es, M),
    A is A0 + C * M.

mono_value(Pos, Es, M) :-
    foldl(pow_acc, Pos, Es, 1, M).

pow_acc(X, E, A0, A) :-
    A is A0 * X ^ E.

fits_all(F, Samples) :-
    maplist(fits_one(F), Samples).

fits_one(F, Pos-V) :-
    eval_f(F, Pos, X),
    X =:= V.

%  Description length: structure plus the size of every coefficient.
penalty(poly(Terms), P) :-
    findall(Es-C, ( member(Es-C, Terms), C =\= 0 ), NZ),
    length(NZ, L),
    findall(S, ( member(Es-_, NZ), sum_list(Es, S) ), Ss),
    sum_list(Ss, SE),
    findall(Z, ( member(_-C, NZ), rat_size(C, Z) ), Zs),
    sum_list(Zs, SZ),
    P is 2 * L + SE + SZ.
penalty(geo(A, B, C), P) :-
    rat_size(A, SA),
    rat_size(B, SB),
    rat_size(C, SC),
    P is 3 + SA + SB + SC.
penalty(periodic(N, Fs), P) :-
    maplist(penalty, Fs, Ps),
    sum_list(Ps, S),
    P is 4 * N + S.

rat_size(R, S) :-
    rat_num(R, N),
    rat_den(R, D),
    bits(N, BN),
    bits(D, BD),
    S is BN + BD - 1.

%  the number of halvings of |N| before 0, plus one
bits(N, B) :-
    A is abs(N),
    if_commit(A =:= 0, B = 1, B is msb(A) + 2).

% ---------------------------------------------------------------------------
% Linear algebra

%  solve_linear(+Rows, +Rhs, -Maybe): the exact solution of A x = b, if the
%  system is consistent and has a unique solution.
solve_linear(Rows, Rhs, M) :-
    if_commit(Rows = [R0|_], length(R0, N), N = 0),
    maplist(augment, Rows, Rhs, Aug),
    solve_go(0, N, Aug, M).

augment(R, V, A) :-
    conc(R, [V], A).

solve_go(Col, N, Mx, M) :-
    if_commit(Col =:= N,
              if_commit(maplist(consistent_row(N), Mx),
                        ( N1 is N - 1,
                          findall(X, ( between(0, N1, I), I1 is I + 1, nth_det(I1, Mx, just(Row)), last_of(Row, X) ), Xs),
                          M = just(Xs) ),
                        M = nothing),
              ( numbered_list(Mx, 0, NM),
                Col1 is Col + 1,
                if_commit(( member(I-R, NM), I >= Col, nth_det(Col1, R, just(X)), X =\= 0 ),
                          ( swap_rows(Col, I, Mx, Sw),
                            nth_det(Col1, Sw, just(PR)),
                            nth_det(Col1, PR, just(PV)),
                            maplist(div_by(PV), PR, PRow),
                            numbered_list(Sw, 0, NSw),
                            maplist(elim_row(Col, Col1, PRow), NSw, Mx1),
                            solve_go(Col1, N, Mx1, M) ),
                          M = nothing) )).

consistent_row(N, R) :-
    take(N, R, Front),
    last_of(R, L),
    if_commit(all_zero(Front), L =:= 0, true).

all_zero([]).
all_zero([X|Xs]) :-
    X =:= 0,
    all_zero(Xs).

div_by(P, X, Y) :-
    Y is X rdiv P.

elim_row(Col, Col1, PRow, I-R, R1) :-
    if_commit(I =:= Col, R1 = PRow,
              ( nth_det(Col1, R, just(F)), maplist(sub_scaled(F), R, PRow, R1) )).

sub_scaled(F, A, B, C) :-
    C is A - F * B.

swap_rows(I, J, Xs, Out) :-
    if_commit(I =:= J, Out = Xs,
              ( I1 is I + 1, J1 is J + 1,
                nth_det(I1, Xs, just(XI)), nth_det(J1, Xs, just(XJ)),
                numbered_list(Xs, 0, NXs),
                maplist(swap_pick(I, J, XI, XJ), NXs, Out) )).

swap_pick(I, J, XI, XJ, K-X, Y) :-
    if_commit(K =:= I, Y = XJ, if_commit(K =:= J, Y = XI, Y = X)).

%  Monomials over M indices, in order of total degree up to D.
monomials(M, D, Es) :-
    vectors(M, D, Vs),
    findall(k(S, R)-E, ( member(E, Vs), sum_list(E, S), S =< D, rev(E, R) ), Keyed),
    msort(Keyed, Sorted),
    pairs_values(Sorted, Es).

vectors(K, D, Vs) :-
    if_commit(K =:= 0, Vs = [[]],
              ( K1 is K - 1, vectors(K1, D, Rs),
                findall([X|R], ( between(0, D, X), member(R, Rs) ), Vs) )).

row_of(Basis, Pos-_, Row) :-
    findall(V, ( member(Es, Basis), mono_value(Pos, Es, V) ), Row).

%  Fit a polynomial with the given monomials on the first samples (as many
%  as monomials, linearly independent), then require the others to match.
fit_poly(Basis, Samples, M) :-
    length(Basis, K),
    choose_independent(Basis, K, Samples, [], MC),
    if_commit(MC = just(Fitted),
              ( maplist(row_of(Basis), Fitted, Rows),
                pairs_values(Fitted, Rhs),
                solve_linear(Rows, Rhs, MS),
                if_commit(MS = just(Coeffs),
                          ( pairs_keys_values(Pairs, Basis, Coeffs),
                            findall(E-C, ( member(E-C, Pairs), C =\= 0 ), NZ),
                            F = poly(NZ),
                            length(Samples, L),
                            Held is L - K,
                            if_commit(( Held >= 1, fits_all(F, Samples) ),
                                      ( penalty(F, P), M = just(found(F, K, Held, P)) ),
                                      M = nothing) ),
                          M = nothing) ),
              M = nothing).

choose_independent(Basis, K, Ss, Acc, M) :-
    length(Acc, LA),
    if_commit(LA =:= K, ( rev(Acc, R), M = just(R) ),
              if_commit(Ss = [S|Rest],
                        ( rev([S|Acc], Cand),
                          maplist(row_of(Basis), Cand, Rows),
                          mx_rank(Rows, Rk),
                          length(Rows, LR),
                          if_commit(Rk =:= LR,
                                    choose_independent(Basis, K, Rest, [S|Acc], M),
                                    choose_independent(Basis, K, Rest, Acc, M)) ),
                        M = nothing)).

mx_rank(Rs, N) :-
    echelon(Rs, Ech),
    findall(R, ( member(R, Ech), has_nonzero(R) ), NZ),
    length(NZ, N).

has_nonzero(R) :-
    if_commit(( member(X, R), X =\= 0 ), true, fail).

echelon(Rs, E) :-
    if_commit(Rs == [], E = [],
              if_commit(( member(P, Rs), P = [H|_], H =\= 0 ),
                        ( P = [HP|TP],
                          findall(O, ( member(R, Rs), R \== P, R = [HR|TR],
                                       maplist(elim_scaled(HR, HP), TR, TP, O) ), Others),
                          findall(O, ( member(O, Others), O \== [] ), Others1),
                          echelon(Others1, E1),
                          E = [P|E1] ),
                        ( findall(T, ( member(R, Rs), R = [_|T], T \== [] ), Tails),
                          echelon(Tails, E) ))).

elim_scaled(HR, HP, A, B, C) :-
    C is A - (HR rdiv HP) * B.

%  a * b^i + c from consecutive single-index samples.
fit_geo(Samples, M) :-
    if_commit(( Samples = [[I0]-X0, [I1]-X1, [I2]-X2, _|_],
                I1 =:= I0 + 1, I2 =:= I1 + 1, X1 =\= X0 ),
              ( D1 is X1 - X0,
                D2 is X2 - X1,
                BR is D2 rdiv D1,
                rat_den(BR, Den),
                rat_num(BR, B),
                if_commit(( Den =:= 1, B =\= 0, B =\= 1 ),
                          ( rat_pow(B, I0, BI0),
                            A is D1 rdiv (BI0 * (B - 1)),
                            C is X0 - A * BI0,
                            F = geo(A, B, C),
                            if_commit(fits_all(F, Samples),
                                      ( length(Samples, L), H is L - 3, penalty(F, P),
                                        M = just(found(F, 3, H, P)) ),
                                      M = nothing) ),
                          M = nothing) ),
              M = nothing).

%  Different affine formulas for i mod 2 = 0 and 1 (each with held-out samples).
fit_periodic(Samples, M) :-
    by_class(Samples, 0, C0),
    by_class(Samples, 1, C1),
    best_affine(C0, M0),
    best_affine(C1, M1),
    if_commit(( M0 = just(found(F0, Fd0, H0, _)), M1 = just(found(F1, Fd1, H1, _)) ),
              ( F = periodic(2, [F0, F1]),
                if_commit(fits_all(F, Samples),
                          ( Fd is Fd0 + Fd1, H is H0 + H1, penalty(F, P), M = just(found(F, Fd, H, P)) ),
                          M = nothing) ),
              M = nothing).

by_class(Samples, R, Cls) :-
    findall([I]-V, ( member([I]-V, Samples), I mod 2 =:= R ), Cls).

best_affine(Ss, M) :-
    monomials(1, 0, B0),
    monomials(1, 1, B1),
    fit_poly(B0, Ss, MA),
    fit_poly(B1, Ss, MB),
    findall(P-Fd, ( member(just(Fd), [MA, MB]), Fd = found(_, _, _, P) ), Ps),
    sort(1, @=<, Ps, Sorted),
    if_commit(Sorted = [_-Best|_], M = just(Best), M = nothing).

%  discover(+Samples, -Maybe): the best formula for the samples, or nothing
%  (no_formula).
discover(Samples, M) :-
    if_commit(Samples == [], M = nothing,
              ( Samples = [Pos0-_|_],
                length(Pos0, Mi),
                if_commit(Mi =:= 1, MaxDeg = 4, MaxDeg = 2),
                findall(R, ( between(0, MaxDeg, D), monomials(Mi, D, B), fit_poly(B, Samples, R) ), Polys),
                sort(1, @=<, Samples, Sorted),
                if_commit(Mi =:= 1,
                          ( fit_geo(Sorted, G), fit_periodic(Sorted, Pe), Others = [G, Pe] ),
                          Others = []),
                conc(Polys, Others, All),
                findall(k(P, Fd)-F, ( member(just(F), All), F = found(_, Fd, _, P) ), Cands),
                sort(1, @=<, Cands, SC),
                if_commit(SC = [_-Best|_], M = just(Best), M = nothing) )).

% ---------------------------------------------------------------------------
% Terms

rat_t(R, comp('/', [int(N), int(D)])) :-
    rat_num(R, N),
    rat_den(R, D).

formula_term(poly(Terms), comp(poly, [L])) :-
    maplist(mono_t, Terms, Ms),
    mk_list(Ms, atom('[]'), L).
formula_term(geo(A, B, C), comp(geo, [AT, int(B), CT])) :-
    rat_t(A, AT),
    rat_t(C, CT).
formula_term(periodic(P, Fs), comp(periodic, [int(P), L])) :-
    maplist(formula_term, Fs, Ts),
    mk_list(Ts, atom('[]'), L).

mono_t(Es-C, comp(m, [EL, CT])) :-
    maplist(int_t, Es, ETs),
    mk_list(ETs, atom('[]'), EL),
    rat_t(C, CT).

int_t(I, int(I)).

%  formula_from_term(+Term, -Maybe)
formula_from_term(T, M) :-
    if_commit(ff_term(T, F), M = just(F), M = nothing).

ff_term(T, F) :-
    if_commit(T = comp(poly, [L]),
              ( list_t_of(L, Ms), maplist(ff_mono, Ms, Terms), F = poly(Terms) ),
    if_commit(T = comp(geo, [AT, int(B), CT]),
              ( ff_rat(AT, A), ff_rat(CT, C), F = geo(A, B, C) ),
    if_commit(T = comp(periodic, [int(P), L]),
              ( list_t_of(L, Ts), maplist(ff_term, Ts, Fs), F = periodic(P, Fs) ),
              fail))).

ff_mono(T, Es-C) :-
    T = comp(m, [EL, CT]),
    list_t_of(EL, ETs),
    maplist(int_t, Es, ETs),
    ff_rat(CT, C).

ff_rat(comp('/', [int(N), int(D)]), R) :-
    D =\= 0,
    R is N rdiv D.

list_t_of(T, L) :-
    if_commit(T == atom('[]'), L = [],
              ( T = comp('.', [H, R]), list_t_of(R, L0), L = [H|L0] )).

%  expr_term(+Formula, +Vars, -Term): an integer arithmetic expression for
%  is/2 over index variables.  The formula is integer-valued where it is
%  used, so the division by the common denominator is exact.
expr_term(poly(Terms), Vars, E) :-
    findall(D, ( member(_-C, Terms), rat_den(C, D) ), Ds),
    foldl(lcm_acc, Ds, 1, L),
    findall(X, ( member(Es-C, Terms), CN is C * L, rat_num(CN, N),
                 mono_t_expr(Vars, Es, MT), times_t(int(N), MT, X) ), Xs),
    sum_t(Xs, Num),
    if_commit(L =:= 1, E = Num, E = comp('//', [Num, int(L)])).
expr_term(geo(A, B, C), Vars, E) :-
    rat_den(A, DA),
    rat_den(C, DC),
    foldl(lcm_acc, [DA, DC], 1, L),
    Vars = [I|_],
    AN0 is A * L, rat_num(AN0, AN),
    CN0 is C * L, rat_num(CN0, CN),
    times_t(int(AN), comp('^', [int(B), I]), X1),
    sum_t([X1, int(CN)], Num),
    if_commit(L =:= 1, E = Num, E = comp('//', [Num, int(L)])).
expr_term(periodic(P, Fs), Vars, E) :-
    Vars = [I|_],
    numbered_list(Fs, 0, NFs),
    findall(X, ( member(R-G, NFs),
                 Sel = comp('-', [int(1), comp(min, [int(1), comp(abs, [comp('-', [comp(mod, [I, int(P)]), int(R)])])])]),
                 expr_term(G, Vars, GE),
                 times_t(Sel, GE, X) ), Xs),
    sum_t(Xs, E).

lcm_acc(D, A0, A) :-
    lcm_i(A0, D, A).

mono_t_expr(Vars, Es, T) :-
    mono_vars(Vars, Es, Xs),
    if_commit(Xs == [], T = int(1), ( Xs = [X|Rest], foldl(times_acc, Rest, X, T) )).

%  zip vars es, each variable repeated by its exponent
mono_vars(Vars, Es, Xs) :-
    zip_short(Vars, Es, Pairs),
    findall(V, ( member(V-E, Pairs), between(1, E, _) ), Xs).

zip_short(As, Bs, Ps) :-
    zip_short_(As, Bs, Ps).

zip_short_([], _, []).
zip_short_([A|As], Bs, Ps) :-
    if_commit(Bs = [B|Bs1], ( zip_short_(As, Bs1, Ps1), Ps = [A-B|Ps1] ), Ps = []).

times_acc(B, A, comp('*', [A, B])).

times_t(C, X, T) :-
    if_commit(C == int(1), T = X,
              if_commit(X == int(1), T = C, T = comp('*', [C, X]))).

sum_t(Xs, T) :-
    if_commit(Xs = [X|Rest], foldl(plus_acc, Rest, X, T), T = int(0)).

plus_acc(B, A, comp('+', [A, B])).

%  A readable formula over index names i, j, k, ...
show_formula(F, S) :-
    expr_term(F, [atom(i), atom(j), atom(k), atom(l), atom(m), atom(n)], E),
    show_term_q(E, S).
