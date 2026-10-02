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
- **Covariance propagation, cases 1 to 4** (`MscProofs/CovariancePropagation.lean`). Covariance
  formulas for sums of known gains times: pairwise independent noise (case 1), the cross product
  of a common bias with a case 1 sum (case 2), the cross product of fresh noise with a case 1 sum
  (case 3), and a case 1 sum (case 4). Each is stated as a recursion on a few running matrix
  sums, so on-board software can propagate it with fixed-size state instead of buffering the
  whole history.
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

Koja, Rian. [On methods for in-flight alignment of inertial navigation systems](http://mtc-m21c.sid.inpe.br/col/sid.inpe.br/mtc-m21c/2019/02.06.02.41/doc/publicacao.pdf).
Master's thesis, Instituto Nacional de Pesquisas Espaciais (INPE), São José dos Campos, 2019.

BibTeX entry (also in [thesis.bib](thesis.bib)):

<details>
<summary>Show BibTeX</summary>

```bibtex
@MastersThesis{Koja:2019:MeInAl,
               author = "Koja, Rian",
                title = "On methods for in-flight alignment of inertial navigation
                         systems",
               school = "Instituto Nacional de Pesquisas Espaciais (INPE)",
                 year = "2019",
              address = "S{\~a}o Jos{\'e} dos Campos",
                month = feb,
                 date = "2019-02-21",
             keywords = "navega{\c{c}}{\~a}o inercial, alinhamento em voo,
                         navega{\c{c}}{\~a}o auxiliada por GPS, propaga{\c{c}}{\~a}o de
                         covari{\^a}ncia, inertial navigation, in-flight alignment,
                         GPS-aided navigation, covariance propagation.",
             abstract = "This work reviews and adapts the framework for in-flight attitude
                         initialization of an Inertial Navigation System with
                         Position-Velocity Integration formulas (PIF and VIF), which are
                         based on measurements from a GPS receiver and inertial sensors. It
                         is shown that some shortcomings of such methods are more critical
                         for a simplified comparison algorithm (TRIAD), which in turn helps
                         to create a derived method (FIL), based on some logical conditions
                         checks which allow precluding large alignment errors. The
                         algorithms are then analyzed by developing an original on-line
                         error estimation method, based on an estimation of the covariance
                         of the involved vectors yielding a direction error for the
                         vectors, which allows a decision criterion for online convergence
                         declaration employed for two additional methods (OPT and OPTc).
                         Results are validated with simulated data and Monte-Carlo tests
                         are employed to assess the performance and validate some
                         assumptions associated with those methods.",
            committee = "Kuga, H{\'e}lio Koiti (presidente) and Leite Filho, Waldemar de
                         Castro (orientador) and Chagas, Ronan Arraes Jardim and Waldmann,
                         Jacques",
             language = "en",
                pages = "263",
                  ibi = "8JMKD3MGP3W34R/3SMGTAP",
                  url = "http://urlib.net/ibi/8JMKD3MGP3W34R/3SMGTAP",
           targetfile = "publicacao.pdf",
        urlaccessdate = "2026, Oct. 02"
}
```

</details>
