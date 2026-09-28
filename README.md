# msc_proofs

Lean 4 formalization of results from my master thesis. Work in progress.

## Results

- **Covariance of a cross product.** For independent zero-mean random vectors in ℝ³, the
  covariance of their cross product depends only on their two covariance matrices, through an
  explicit bilinear operator `⊠`. Formalized so far: the algebraic core (rank-one identity),
  commutativity and scaling. See `MscProofs/BoxTimes.lean`.

## Checking

```sh
lake exe cache get
lake build --wfail
lake lint
```

CI also re-checks the proofs with the [nanoda](https://github.com/ammkrn/nanoda_lib) external
type checker.
