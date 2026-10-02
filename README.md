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
                         assumptions associated with those methods. RESUMO: Este trabalho
                         revisa e adapta os m{\'e}todos de inicializa{\c{c}}{\~a}o de
                         atitude em voo de um Sistema de Navega{\c{c}}{\~a}o Inercial via
                         F{\'o}rmulas de Integra{\c{c}}{\~a}o
                         Posi{\c{c}}{\~a}o-Velocidade (PIF e VIF), os quais s{\~a}o
                         baseados em medi{\c{c}}{\~o}es provenientes de um receptor GPS e
                         sensores inerciais. S{\~a}o apresentadas algumas
                         limita{\c{c}}{\~o}es desses m{\'e}todos, que s{\~a}o mais
                         cr{\'{\i}}ticas para um algoritmo de compara{\c{c}}{\~a}o
                         simplificado (TRIAD), o qual permite desenvolver um m{\'e}todo
                         derivado (FIL), baseado em verifica{\c{c}}{\~o}es de
                         condi{\c{c}}{\~o}es l{\'o}gicas que mitigam erros grandes de
                         alinhamento. Estes algoritmos s{\~a}o ent{\~a}o analisados pelo
                         desenvolvimento de um m{\'e}todo original de
                         estima{\c{c}}{\~a}o de erro embarcado, baseado na
                         covari{\^a}ncia estimada dos vetores envolvidos, produzindo
                         ent{\~a}o um erro de dire{\c{c}}{\~a}o dos vetores, que permite
                         um crit{\'e}rio de declara{\c{c}}{\~a}o de converg{\^e}ncia
                         empregado em dois m{\'e}todos adicionais (OPT e OPTc). Resultados
                         s{\~a}o validados com dados simulados e testes de Monte-Carlo
                         s{\~a}o empregados para aferir o desempenho e validar
                         hip{\'o}teses associadas a esses m{\'e}todos.",
            committee = "Kuga, H{\'e}lio Koiti (presidente) and Leite Filho, Waldemar de
                         Castro (orientador) and Chagas, Ronan Arraes Jardim and Waldmann,
                         Jacques",
         englishtitle = "Sobre m{\'e}todos de alinhamento em voo de sistemas de
                         navega{\c{c}}{\~a}o inercial",
             language = "en",
                pages = "263",
                  ibi = "8JMKD3MGP3W34R/3SMGTAP",
                  url = "http://urlib.net/ibi/8JMKD3MGP3W34R/3SMGTAP",
           targetfile = "publicacao.pdf",
        urlaccessdate = "2026, Oct. 02"
}
```

</details>
