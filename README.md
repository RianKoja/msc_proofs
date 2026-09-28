# msc_proofs

Lean 4 formalization of results from my master thesis. Work in progress.

## Results

All results below are from my master thesis.

- **Covariance of a cross product** (`MscProofs/BoxTimes.lean`, `MscProofs/Covariance.lean`).
  For independent zero-mean square-integrable random vectors in ℝ³, the covariance of their
  cross product depends only on their two covariance matrices, through an explicit bilinear
  operator `⊠`. Also formalized: `⊠` is commutative and bilinear, scaling the vectors by `a` and
  `b` scales the covariance by `a²b²`, and linear maps applied to either factor or to the cross
  product propagate as expected.
- **Multivariate Chebyshev inequality** (`MscProofs/Chebyshev.lean`). A random vector deviates
  from its mean by at least `k √(tr K)` with probability at most `1/k²`. The formal statement
  needs `tr K > 0`; a counterexample shows the condition cannot be dropped.
- **Covariance propagation, case 1** (`MscProofs/CovariancePropagation.lean`). The covariance
  of a sum of known gains times pairwise independent noise, in closed form and as a one-step
  recursion suitable for on-board computation.
- **Trend line for the v vectors** (`MscProofs/TrendLine.lean`). Closed form, with a `sinc`
  term, for the norm of the integrated gravity vector of a stationary vehicle seen from the
  rotating Earth frame.

## Checking

```sh
lake exe cache get
lake build --wfail
lake lint
```

CI also re-checks the proofs with the [nanoda](https://github.com/ammkrn/nanoda_lib) external
type checker.

## Reference

Koja, Rian. "On methods for in-flight alignment of inertial navigation systems." (2019).
Master's thesis.

```bibtex
@mastersthesis{koja2019,
  author = {Koja, Rian},
  title  = {On methods for in-flight alignment of inertial navigation systems},
  year   = {2019}
}
```
