# algebraplop2 proof rules

Every `algebraplop2 program` run writes `OUT` and `OUT.proof`. The output is
written only if the independent checker (`src/aproof.pl`) accepts the proof.
The checker does not call the discovery code (`discover/2` in `src/algebra.pl`).
It reads the source program, evaluates the source's own arithmetic with
detlog2's `evalArith`, and runs the source with detlog2's reference engine.

A proof is a list of Prolog terms, one step per rewrite.

## Formulas

Formulas are exact rationals, in one of three families:

| term | meaning |
| --- | --- |
| `poly([m(Exps, N/D), ...])` | a sum of monomials over the position indices |
| `geo(N/D, B, N/D)` | `a * b^i + c` |
| `periodic(P, [F0, ..., F(P-1)])` | `F(i mod P)` |

`fit` uses Gaussian elimination over the rationals and ranks candidate
formulas by a description-length penalty. A fit is reported only when at
least one sample was held out of the fit and the formula reproduces it.

## Steps

### `fit(Samples, F)`

The step is **verified_on** the samples. `F` reproduces every sample exactly,
and at least one sample was not used to fit it. This is evidence, not a
proof for positions outside the samples, so the step is labelled `verified_on`.

### `induction(P/2, F, Clause)`

The step is **proved** for every position `N >= B`. The source must have
exactly two clauses:

```prolog
p(B, VB).
p(N, V) :- N > B, N1 is N - 1, p(N1, V1), V is E.
```

- Base case: `F(B) = VB`.
- `E` mentions only `N`, `N1` and `V1`.
- `E` is evaluated at two values of `V1` for each check point, which reads off
  `E = a*V1 + g(N)`. The coefficient `a` must be the same at every point.
- Step identity: `F(N) = a*F(N-1) + g(N)`.
  - When `F` is a polynomial of degree d, `g` is polynomial (it is checked at
    deg+3 points), so checking the identity at deg+3 points proves it.
  - For `geo`, the identity is checked symbolically on the coefficients.

`Clause` must be the template `p__formula(N, V) :- N >= B, V is Expr`. `Expr`
is `F` as integer arithmetic, with denominators cleared by `// LCD`.

### `exhaustive(P/2, Lo, Hi, F, Clause)`

The step is **verified_on(Lo..Hi)**. The source is run (first answer) at every
position in `Lo..Hi`, and each value must equal `F`. `Clause` carries the
guard `Lo =< N, N =< Hi`.

### `inverse(P/2, F, Lo, Hi | inf, Clause)`

The formula's own step (`induction` or `exhaustive`) must cover the range. `F`
must be integer affine (`a*i + c`, with `a` not 0). `Clause` is the template:

```prolog
p__inverse(V, N) :- integer(V), D is V - c, D mod a =:= 0, N is D // a, N >= Lo, ...
```

### `loop(P/2, ClauseIndex, NewClause, LoopClause)`

Source clause `ClauseIndex` has the form
`q(.., Vs) :- findall(V, (between(L, H, I), p(I, V)), Vs)`. It is replaced by
a splice-index loop over `p__formula`. The loop has no choicepoint: it counts
`I` from `L` to `H` and appends one value per index.
`P`'s formula must be proved (`induction`) or verified on a domain covering
the loop.

### `r_spec(...)`

These are provenance facts. They are copied into the output and checked for
coverage.

## Coverage

The output must be exactly the following, matched up to variable renaming:

- the source clauses, except clauses replaced by `loop`;
- one justified clause per step;
- the `r_spec` facts.

Clauses with no justification are rejected.
