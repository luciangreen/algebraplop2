# algebraplop2

algebraplop2 is [mnns](https://github.com/luciangreen/mnns)'s AlgebraPLOp, redone in
the style of [plop2](https://github.com/luciangreen/plop2) and
[detlog2](https://github.com/luciangreen/detlog2). It replaces positional
computation with a closed formula, and it gives a checked proof for every rewrite.

- **Formulas from samples:** polynomials in one or more indices, `a*b^i + c`,
  and period-2 formulas. Fitting uses exact rationals, with held-out samples.
- **Formulas from programs:** for a predicate `p(Position, Value)`, the formula
  is *proved by induction* when `p` is a first-order recurrence. Otherwise it
  is verified on a domain.
- **Inverses** of integer affine formulas (`p__inverse(V, N)`).
- **Splice-index loops:** `findall(V, (between(L,H,I), p(I,V)), Vs)` becomes a
  deterministic loop over `p__formula`, with no choicepoints and no cuts.

## Build

algebraplop2 is written in Haskell. Programs, examples and proofs are written
in Prolog. It compiles against detlog2's sources.

```sh
git clone https://github.com/luciangreen/detlog2 ../detlog2   # or set DETLOG2_DIR
runghc Build.hs            # builds build/algebraplop2
runghc Build.hs test       # builds, then runs tests/Cli.hs
runghc Build.hs check-ios  # re-runs the 200 recorded input/output pairs in io/ios.txt
```

## Use

```sh
algebraplop2 samples "2,4,8,16,32"
#   formula: 2 * 2 ^ i      verified_on(samples)
algebraplop2 program examples/sequences.pl tri/2 -o out.pl
#   formula: (i + i * i) // 2     proved(induction)
algebraplop2 program examples/sequences.pl odd/2 -o out.pl
#   writes odd__formula/2, odd__inverse(V, N) and odds__loop
algebraplop2 proof-check examples/sequences.pl out.pl out.pl.proof
```

With `--mnns DIR`, it also reports what mnns's own AlgebraPLOp finds for the
same samples, for comparison.

## Proofs

Every `program` output comes with `OUT.proof`, and nothing is written unless
the checker accepts it. Each claim is labelled with what backs it:

- `proved(induction)`: the base case and the step identity, read from the
  source's own arithmetic;
- `verified_on(Lo..Hi)`: the source was run on every position in the range;
- `verified_on(samples)`: the formula was fitted, with held-out samples.

The rules are in [docs/proof_rules.md](docs/proof_rules.md).

## Input/output pairs

[`io/ios.txt`](io/ios.txt) holds 200 recorded commands and their outputs.
CI re-runs all of them.
