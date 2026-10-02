# Extensions beyond the thesis

The results below are **not in the master thesis**. They are new properties of the `⊠` operator,
all formally proven in [`MscProofs/BoxTimesExtensions.lean`](MscProofs/BoxTimesExtensions.lean).
To cite them, please cite this repository (see the end of this file).

Notation: `A`, `B`, `C` are symmetric `3 × 3` matrices, `M` is any `3 × 3` matrix, `Q` is
orthogonal (`QᵀQ = I`), `u`, `v`, `x` are 3-vectors, `[u]ₓ` is the cross-product matrix
(`[u]ₓ v = u × v`), `adj` is the adjugate and `⊗` the Kronecker product. Results 6, 7, 11 and 13
are for real matrices, 1 and 15 are about random vectors, and 28 is shown with integer matrices;
all other identities hold over any commutative ring. Symmetry is needed because `⊠` only reads the
upper triangle of its arguments; results that hold without it say so.

Results are listed in order of expected importance.

| # | Property | Statement | Lean |
|---|----------|-----------|------|
| 1 | Cross-product covariance with non-zero means | for independent square-integrable `X`, `Y` with means `m`, `m'`: `Cov[X × Y] = (Cov[X] + m mᵀ) ⊠ (Cov[Y] + m' m'ᵀ) − (m mᵀ) ⊠ (m' m'ᵀ)` | `covMat_cross_of_mean` |
| 2 | Polarization of the adjugate | `A ⊠ B = adj(A + B) − adj A − adj B` | `boxTimes_eq_adjugate` |
| 3 | Adjugate identity | `A ⊠ A = 2 adj A` | `boxTimes_self` |
| 4 | Coordinate-free formula | `A ⊠ B = AB + BA − tr(A) B − tr(B) A + (tr A tr B − tr(AB)) I` | `boxTimes_eq` |
| 5 | Kronecker representation | `A ⊠ B = L (A ⊗ B) Lᵀ`, with `L` the `3 × 9` Levi-Civita matrix `L_{i,(j,k)} = εᵢⱼₖ` | `boxTimes_eq_kronecker` |
| 6 | Positive semidefiniteness | `A, B ⪰ 0 ⇒ A ⊠ B ⪰ 0` | `posSemidef_boxTimes` |
| 7 | Positive definiteness | `A, B ≻ 0 ⇒ A ⊠ B ≻ 0` | `posDef_boxTimes` |
| 8 | Congruence | `(M A Mᵀ) ⊠ (M B Mᵀ) = adj(M)ᵀ (A ⊠ B) adj(M)` | `boxTimes_congr` |
| 9 | Orthogonal equivariance | `(Q A Qᵀ) ⊠ (Q B Qᵀ) = Q (A ⊠ B) Qᵀ` | `boxTimes_orthogonal` |
| 10 | Joint eigenvalues | `(Q diag(p) Qᵀ) ⊠ (Q diag(q) Qᵀ) = Q diag(p₁q₂ + p₂q₁, p₀q₂ + p₂q₀, p₀q₁ + p₁q₀) Qᵀ` | `boxTimes_diagonalize` |
| 11 | Loewner monotonicity | `A ⪯ A'`, `B ⪰ 0 ⇒ A ⊠ B ⪯ A' ⊠ B` | `posSemidef_boxTimes_sub` |
| 12 | Trace identity | `tr(A ⊠ B) = tr A tr B − tr(AB)` | `trace_boxTimes` |
| 13 | Trace bounds | `A, B ⪰ 0 ⇒ 0 ≤ tr(A ⊠ B) ≤ tr A tr B` | `trace_boxTimes_mem_Icc` |
| 14 | Identity argument | `I ⊠ B = tr(B) I − B` | `one_boxTimes` |
| 15 | Isotropic noise | for independent zero-mean `X`, `Y` with `Cov[Y] = σ² I`: `Cov[X × Y] = σ² (tr(Cov[X]) I − Cov[X])` | `covMat_cross_isotropic` |
| 16 | Rank-one argument | `(u uᵀ) ⊠ B = [u]ₓ B [u]ₓᵀ` | `vecMulVec_boxTimes` |
| 17 | Quadratic-form duality | `xᵀ (A ⊠ B) x = tr(A (B ⊠ x xᵀ))` | `dotProduct_boxTimes_mulVec` |
| 18 | Trilinear symmetry | `tr((A ⊠ B) C) = tr((B ⊠ C) A)`; with commutativity, `tr((A ⊠ B) C)` is symmetric in `A`, `B`, `C` | `trace_boxTimes_mul` |
| 19 | Determinant of a sum | `2 det(A + B) = 2 det A + tr(B (A ⊠ A)) + tr(A (B ⊠ B)) + 2 det B` | `two_mul_det_add` |
| 20 | Inverse relation | `A (A ⊠ A) = 2 det(A) I` | `mul_boxTimes_self` |
| 21 | Determinant as a trace | `tr(A (A ⊠ A)) = 6 det A` | `trace_mul_boxTimes_self` |
| 22 | Adjugate of a square | `adj(A ⊠ A) = 4 det(A) A` | `adjugate_boxTimes_self` |
| 23 | Recovery from the identity | `2A = tr(A ⊠ I) I − 2 (A ⊠ I)` | `two_smul_eq_boxTimes_one` |
| 24 | Diagonal arguments | `diag(p) ⊠ diag(q) = diag(p₁q₂ + p₂q₁, p₀q₂ + p₂q₀, p₀q₁ + p₁q₀)` (any `p`, `q`) | `diagonal_boxTimes` |
| 25 | Triple product | `xᵀ ((u uᵀ) ⊠ (v vᵀ)) x = det[u v x]²` (any `u`, `v`, `x`) | `dotProduct_vecMulVec_boxTimes_mulVec` |
| 26 | Kernel of rank-one products | `((u uᵀ) ⊠ B) u = 0` for any `B`, and `(u uᵀ) ⊠ (u uᵀ) = 0` | `vecMulVec_boxTimes_mulVec_self`, `vecMulVec_boxTimes_self` |
| 27 | Symmetric output | `A ⊠ B` is symmetric for any `A`, `B` | `boxTimes_isSymm` |
| 28 | Non-associativity | `(A ⊠ B) ⊠ C ≠ A ⊠ (B ⊠ C)` in general | `boxTimes_not_assoc` |

## Citing

```bibtex
@misc{koja_msc_proofs,
  author       = {Koja, Rian},
  title        = {msc\_proofs: Lean 4 formalization of results from "On methods for in-flight
                  alignment of inertial navigation systems"},
  howpublished = {\url{https://github.com/RianKoja/msc_proofs}},
  year         = {2026}
}
```
