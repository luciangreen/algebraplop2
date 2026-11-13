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

algebraplop2 is written in cut-free, choicepoint-free SWI-Prolog: no `!`,
`;`, `->`, `\+`, `once/1` or `forall/2` in its source. A decision is
`if_commit/3` (from detlog2's `src/detlog_runtime.pl`), which takes the first
answer of its condition with `findall/3` + `limit/2`, and generators are only
called inside `findall/3`, an `if_commit/3` condition or `once_det/1`.
detlog2's `tools/cutfree.pl` checks every source file in the build. Formulas
use SWI-Prolog's exact rationals.

```sh
git clone https://github.com/luciangreen/detlog2 ../detlog2   # or set DETLOG2_DIR
swipl build.pl             # builds build/algebraplop2 (a saved state)
swipl build.pl test        # builds, runs the cut-free check and tests/cli.pl
swipl build.pl ci          # as test (cloning detlog2 and mnns if needed), then
                           # checks the 200 recorded runs in io/ios.txt
swipl build.pl check-ios   # re-runs the 200 recorded input/output pairs
```

The Haskell version it was ported from is kept in `haskell/`
(`runghc haskell/Build.hs test`). CI builds both and checks that they record
the same 200 outputs (`swipl io/ios.pl compare haskell/io/ios.txt`).

Layout:

- `algebraplop2.pl` - loader and `main`; loads detlog2's Prolog sources
- `src/algebra.pl` - formulas, exact fitting and ranking (port of `AlgebraPLOp2.Algebra`)
- `src/program.pl` - recurrences and sampling (port of `AlgebraPLOp2.Program`)
- `src/aproof.pl` - the independent proof checker (port of `AlgebraPLOp2.Proof`)
- `src/aplop2_cli.pl` - the commands
- `tests/cli.pl`, `io/ios.pl` - end-to-end tests and the 200 recorded runs
- `haskell/` - the Haskell version

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
