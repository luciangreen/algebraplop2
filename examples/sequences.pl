% Positions read from programs: Name(Position, Value).

% Triangular numbers: a first-order recurrence, proved by induction.
tri(0, 0).
tri(N, T) :- N > 0, N1 is N - 1, tri(N1, T1), T is T1 + N.

% Powers of two: a * b^n + c, proved by induction.
pow2(0, 1).
pow2(N, V) :- N > 0, N1 is N - 1, pow2(N1, V1), V is 2 * V1.

% Odd numbers: affine, so it also has an inverse.
odd(0, 1).
odd(N, V) :- N > 0, N1 is N - 1, odd(N1, V1), V is V1 + 2.

% Sums of squares: a cubic closed form, proved by induction.
sumsq(0, 0).
sumsq(N, S) :- N > 0, N1 is N - 1, sumsq(N1, S1), S is S1 + N * N.

% 3 * 2^n - 1 from a recurrence with a constant term.
grow(0, 2).
grow(N, V) :- N > 0, N1 is N - 1, grow(N1, V1), V is 2 * V1 + 1.

% Squares written directly: no recurrence, so verified on a domain.
sq(N, V) :- V is N * N.

% Fibonacci: second order; none of the formula shapes fits (no_formula).
fib(0, 0).
fib(1, 1).
fib(N, F) :- N > 1, N1 is N - 1, N2 is N - 2, fib(N1, F1), fib(N2, F2), F is F1 + F2.

% Loops over positions: become splice-index loops when the formula is proved.
tris(L, H, Ts) :- findall(T, (between(L, H, I), tri(I, T)), Ts).
odds(H, Vs) :- findall(V, (between(0, H, I), odd(I, V)), Vs).
