/-
Copyright (c) 2026 Rian Koja. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rian Koja
-/
import MscProofs.Covariance
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Further properties of Koja's box-times operator

Properties of `⊠` beyond those stated in the thesis. Most identities assume symmetric arguments,
since `⊠` only reads the upper triangle of its inputs. The results are listed, with their
statements in conventional notation, in `EXTENSIONS.md`.
-/
namespace Koja

open Matrix MeasureTheory ProbabilityTheory
open scoped Kronecker

section Algebra

variable {R : Type*} [CommRing R] {A B C : Matrix (Fin 3) (Fin 3) R}

omit [CommRing R] in
lemma entries_of_isSymm (h : A.IsSymm) : A 1 0 = A 0 1 ∧ A 2 0 = A 0 2 ∧ A 2 1 = A 1 2 :=
  ⟨h.apply 0 1, h.apply 0 2, h.apply 1 2⟩

/-- Proves a `3 × 3` matrix identity entry by entry, by polynomial arithmetic. -/
local macro "entrywise" : tactic => `(tactic| (
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boxTimes, trace_fin_three, adjugate_fin_three, det_fin_three, mul_apply,
      Fin.sum_univ_three, *] <;> ring))

/-- The box-times operator always returns a symmetric matrix. -/
theorem boxTimes_isSymm (A B : Matrix (Fin 3) (Fin 3) R) : (A ⊠ B).IsSymm :=
  IsSymm.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl

lemma boxTimes_sub_left (A A' B : Matrix (Fin 3) (Fin 3) R) :
    (A - A') ⊠ B = A ⊠ B - A' ⊠ B := by
  entrywise

/-- Koja's isotropic property: `1 ⊠ B = tr(B) 1 - B`. -/
theorem one_boxTimes (hB : B.IsSymm) : 1 ⊠ B = B.trace • 1 - B := by
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  entrywise

/-- Koja's trace identity: `tr(A ⊠ B) = tr A tr B - tr(A B)`. -/
theorem trace_boxTimes (hA : A.IsSymm) (hB : B.IsSymm) :
    (A ⊠ B).trace = A.trace * B.trace - (A * B).trace := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  simp [boxTimes, trace_fin_three, mul_apply, Fin.sum_univ_three, *]
  ring

/-- Koja's adjugate identity: `A ⊠ A = 2 adj A`. -/
theorem boxTimes_self (hA : A.IsSymm) : A ⊠ A = (2 : R) • adjugate A := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  entrywise

/-- Koja's polarization identity: `⊠` is the polarization of the adjugate,
`A ⊠ B = adj(A + B) - adj A - adj B`. -/
theorem boxTimes_eq_adjugate (hA : A.IsSymm) (hB : B.IsSymm) :
    A ⊠ B = adjugate (A + B) - adjugate A - adjugate B := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  entrywise

/-- Koja's coordinate-free formula:
`A ⊠ B = A B + B A - tr(A) B - tr(B) A + (tr A tr B - tr(A B)) 1`. -/
theorem boxTimes_eq (hA : A.IsSymm) (hB : B.IsSymm) :
    A ⊠ B = A * B + B * A - A.trace • B - B.trace • A
      + (A.trace * B.trace - (A * B).trace) • 1 := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  entrywise

/-- `A` can be recovered from `A ⊠ 1`: `2 A = tr(A ⊠ 1) 1 - 2 (A ⊠ 1)`. -/
theorem two_smul_eq_boxTimes_one (hA : A.IsSymm) :
    (2 : R) • A = (A ⊠ 1).trace • 1 - (2 : R) • (A ⊠ 1) := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  entrywise

/-- `A (A ⊠ A) = 2 det(A) 1`. -/
theorem mul_boxTimes_self (hA : A.IsSymm) : A * (A ⊠ A) = (2 * A.det) • 1 := by
  rw [boxTimes_self hA, mul_smul_comm, mul_adjugate, smul_smul]

/-- `tr(A (A ⊠ A)) = 6 det A`. -/
theorem trace_mul_boxTimes_self (hA : A.IsSymm) : (A * (A ⊠ A)).trace = 6 * A.det := by
  rw [mul_boxTimes_self hA, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-- `adj(A ⊠ A) = 4 det(A) A`. -/
theorem adjugate_boxTimes_self (hA : A.IsSymm) : adjugate (A ⊠ A) = (4 * A.det) • A := by
  rw [boxTimes_self hA, adjugate_smul, adjugate_adjugate _ (by simp), smul_smul]
  norm_num

/-- Determinant of a sum through `⊠`:
`2 det(A + B) = 2 det A + tr(B (A ⊠ A)) + tr(A (B ⊠ B)) + 2 det B`. -/
theorem two_mul_det_add (hA : A.IsSymm) (hB : B.IsSymm) :
    2 * (A + B).det = 2 * A.det + (B * (A ⊠ A)).trace + (A * (B ⊠ B)).trace + 2 * B.det := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  simp [boxTimes, trace_fin_three, det_fin_three, mul_apply, Fin.sum_univ_three, *]
  ring

lemma isSymm_mul_mul_transpose (hA : A.IsSymm) (M : Matrix (Fin 3) (Fin 3) R) :
    (M * A * Mᵀ).IsSymm := by
  simp [IsSymm, transpose_mul, hA.eq, Matrix.mul_assoc]

/-- Koja's congruence property: `(M A Mᵀ) ⊠ (M B Mᵀ) = adj(M)ᵀ (A ⊠ B) adj(M)`. -/
theorem boxTimes_congr (hA : A.IsSymm) (hB : B.IsSymm) (M : Matrix (Fin 3) (Fin 3) R) :
    (M * A * Mᵀ) ⊠ (M * B * Mᵀ) = (adjugate M)ᵀ * (A ⊠ B) * adjugate M := by
  have hadj : ∀ X : Matrix (Fin 3) (Fin 3) R,
      adjugate (M * X * Mᵀ) = (adjugate M)ᵀ * adjugate X * adjugate M := fun X ↦ by
    rw [adjugate_mul_distrib, adjugate_mul_distrib, ← adjugate_transpose, Matrix.mul_assoc]
  rw [boxTimes_eq_adjugate (isSymm_mul_mul_transpose hA M) (isSymm_mul_mul_transpose hB M),
    boxTimes_eq_adjugate hA hB,
    show M * A * Mᵀ + M * B * Mᵀ = M * (A + B) * Mᵀ by rw [Matrix.mul_add, Matrix.add_mul],
    hadj, hadj, hadj]
  simp only [Matrix.mul_sub, Matrix.sub_mul]

/-- Koja's orthogonal equivariance: for orthogonal `Q`, `(Q A Qᵀ) ⊠ (Q B Qᵀ) = Q (A ⊠ B) Qᵀ`. -/
theorem boxTimes_orthogonal (hA : A.IsSymm) (hB : B.IsSymm) {Q : Matrix (Fin 3) (Fin 3) R}
    (hQ : Qᵀ * Q = 1) : (Q * A * Qᵀ) ⊠ (Q * B * Qᵀ) = Q * (A ⊠ B) * Qᵀ := by
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hadj : adjugate Q = Q.det • Qᵀ := by
    rw [← Matrix.mul_one (adjugate Q), ← hQ', ← Matrix.mul_assoc, adjugate_mul, smul_mul,
      Matrix.one_mul]
  have hdet : Q.det * Q.det = 1 := by
    have := congrArg det hQ
    rwa [det_mul, det_transpose, det_one] at this
  rw [boxTimes_congr hA hB, hadj, transpose_smul, transpose_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hdet, one_smul]

/-- The cross-product (hat) matrix: `crossMatrix u *ᵥ v = u ⨯₃ v`. -/
def crossMatrix (u : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0]

lemma crossMatrix_mulVec (u v : Fin 3 → R) : crossMatrix u *ᵥ v = u ⨯₃ v := by
  ext i
  fin_cases i <;> simp [crossMatrix, cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- Koja's rank-one property: `(u uᵀ) ⊠ B = [u]ₓ B [u]ₓᵀ`, generalizing Koja's identity. -/
theorem vecMulVec_boxTimes (u : Fin 3 → R) (hB : B.IsSymm) :
    vecMulVec u u ⊠ B = crossMatrix u * B * (crossMatrix u)ᵀ := by
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boxTimes, crossMatrix, vecMulVec_apply, mul_apply, vecMul, dotProduct,
      Fin.sum_univ_three, *] <;> ring

/-- `u` lies in the kernel of `(u uᵀ) ⊠ B`, for any `B`. -/
theorem vecMulVec_boxTimes_mulVec_self (u : Fin 3 → R) (B : Matrix (Fin 3) (Fin 3) R) :
    (vecMulVec u u ⊠ B) *ᵥ u = 0 := by
  ext i
  fin_cases i <;> simp [boxTimes, vecMulVec_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem vecMulVec_boxTimes_self (u : Fin 3 → R) : vecMulVec u u ⊠ vecMulVec u u = 0 := by
  rw [boxTimes_vecMulVec, cross_self, vecMulVec_zero]

/-- Koja's triple-product property: `xᵀ ((u uᵀ) ⊠ (v vᵀ)) x = det[u v x]²`. -/
theorem dotProduct_vecMulVec_boxTimes_mulVec (u v x : Fin 3 → R) :
    x ⬝ᵥ ((vecMulVec u u ⊠ vecMulVec v v) *ᵥ x) = (Matrix.det ![u, v, x]) ^ 2 := by
  rw [boxTimes_vecMulVec, ← triple_product_eq_det]
  simp [vecMulVec_apply, mulVec, dotProduct, cross_apply, Fin.sum_univ_three]
  ring

/-- Koja's duality of quadratic forms: `xᵀ (A ⊠ B) x = tr(A (B ⊠ x xᵀ))`. -/
theorem dotProduct_boxTimes_mulVec (hA : A.IsSymm) (hB : B.IsSymm) (x : Fin 3 → R) :
    x ⬝ᵥ ((A ⊠ B) *ᵥ x) = (A * (B ⊠ vecMulVec x x)).trace := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  simp [boxTimes, trace_fin_three, mul_apply, mulVec, dotProduct, vecMulVec_apply,
    Fin.sum_univ_three, *]
  ring

/-- Koja's trilinear symmetry: `tr((A ⊠ B) C)` is symmetric in `A`, `B` and `C`. -/
theorem trace_boxTimes_mul (hA : A.IsSymm) (hB : B.IsSymm) (hC : C.IsSymm) :
    ((A ⊠ B) * C).trace = ((B ⊠ C) * A).trace := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  obtain ⟨c10, c20, c21⟩ := entries_of_isSymm hC
  simp [boxTimes, trace_fin_three, vecMul, dotProduct, Fin.sum_univ_three, *]
  ring

/-- Koja's diagonal formula. -/
theorem diagonal_boxTimes (p q : Fin 3 → R) :
    diagonal p ⊠ diagonal q
      = diagonal ![p 1 * q 2 + p 2 * q 1, p 0 * q 2 + p 2 * q 0, p 0 * q 1 + p 1 * q 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boxTimes, diagonal] <;> ring

/-- Koja's spectral property: if `A` and `B` are diagonalized by the same orthogonal `Q`, with
eigenvalues `p` and `q`, then `Q` diagonalizes `A ⊠ B`, with eigenvalues `pⱼ qₖ + pₖ qⱼ`. -/
theorem boxTimes_diagonalize {Q : Matrix (Fin 3) (Fin 3) R} (hQ : Qᵀ * Q = 1) (p q : Fin 3 → R) :
    (Q * diagonal p * Qᵀ) ⊠ (Q * diagonal q * Qᵀ)
      = Q * diagonal ![p 1 * q 2 + p 2 * q 1, p 0 * q 2 + p 2 * q 0, p 0 * q 1 + p 1 * q 0]
        * Qᵀ := by
  rw [boxTimes_orthogonal (isSymm_diagonal p) (isSymm_diagonal q) hQ, diagonal_boxTimes]

/-- The Levi-Civita symbol as a `3 × 9` matrix, `leviCivita i (j, k) = εᵢⱼₖ`. -/
def leviCivita : Matrix (Fin 3) (Fin 3 × Fin 3) R :=
  of fun i jk ↦ ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]] i jk.1 jk.2

/-- Koja's Kronecker representation: `A ⊠ B = L (A ⊗ B) Lᵀ`, with `L` the Levi-Civita symbol. -/
theorem boxTimes_eq_kronecker (hA : A.IsSymm) (hB : B.IsSymm) :
    A ⊠ B = leviCivita * (A ⊗ₖ B) * leviCivitaᵀ := by
  obtain ⟨a10, a20, a21⟩ := entries_of_isSymm hA
  obtain ⟨b10, b20, b21⟩ := entries_of_isSymm hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boxTimes, leviCivita, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, *] <;> ring

/-- The box-times operator is not associative. -/
theorem boxTimes_not_assoc :
    ¬ ∀ A B C : Matrix (Fin 3) (Fin 3) ℤ, (A ⊠ B) ⊠ C = A ⊠ (B ⊠ C) := by
  intro h
  have := congrFun (congrFun (h 1 1 (diagonal ![1, 0, 0])) 0) 0
  simp [boxTimes, diagonal] at this

end Algebra

/-! ### Order properties (real matrices) -/

section Order

variable {A A' B : Matrix (Fin 3) (Fin 3) ℝ}

lemma isSymm_of_posSemidef (h : A.PosSemidef) : A.IsSymm := by
  rw [IsSymm, ← conjTranspose_eq_transpose_of_trivial]
  exact h.isHermitian

/-- Koja's positivity property: `⊠` maps positive semidefinite matrices to a positive
semidefinite matrix. -/
theorem posSemidef_boxTimes (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊠ B).PosSemidef := by
  rw [boxTimes_eq_kronecker (isSymm_of_posSemidef hA) (isSymm_of_posSemidef hB),
    ← conjTranspose_eq_transpose_of_trivial]
  exact (hA.kronecker hB).mul_mul_conjTranspose_same _

lemma leviCivita_vecMul_injective : Function.Injective (leviCivita (R := ℝ)).vecMul := by
  intro x y h
  have h0 := congrFun h (1, 2)
  have h1 := congrFun h (2, 0)
  have h2 := congrFun h (0, 1)
  simp [vecMul, dotProduct, leviCivita, Fin.sum_univ_three] at h0 h1 h2
  ext i
  fin_cases i <;> assumption

/-- Koja's strict positivity property: `⊠` maps positive definite matrices to a positive
definite matrix. -/
theorem posDef_boxTimes (hA : A.PosDef) (hB : B.PosDef) : (A ⊠ B).PosDef := by
  rw [boxTimes_eq_kronecker (isSymm_of_posSemidef hA.posSemidef)
    (isSymm_of_posSemidef hB.posSemidef), ← conjTranspose_eq_transpose_of_trivial]
  exact (hA.kronecker hB).mul_mul_conjTranspose_same leviCivita_vecMul_injective

/-- Koja's monotonicity property: if `A ≤ A'` in the Loewner order and `B` is positive
semidefinite, then `A ⊠ B ≤ A' ⊠ B`. -/
theorem posSemidef_boxTimes_sub (h : (A' - A).PosSemidef) (hB : B.PosSemidef) :
    (A' ⊠ B - A ⊠ B).PosSemidef := by
  rw [← boxTimes_sub_left]
  exact posSemidef_boxTimes h hB

lemma trace_mul_nonneg (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hB' := isSymm_of_posSemidef hB
  have := (hA.hadamard hB).dotProduct_mulVec_nonneg (fun _ ↦ 1)
  simpa [trace, mul_apply, mulVec, dotProduct, hadamard, hB'.apply] using this

/-- Koja's trace bounds: for positive semidefinite `A` and `B`, `0 ≤ tr(A ⊠ B) ≤ tr A tr B`. -/
theorem trace_boxTimes_mem_Icc (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A ⊠ B).trace ∧ (A ⊠ B).trace ≤ A.trace * B.trace := by
  refine ⟨(posSemidef_boxTimes hA hB).trace_nonneg, ?_⟩
  rw [trace_boxTimes (isSymm_of_posSemidef hA) (isSymm_of_posSemidef hB)]
  linarith [trace_mul_nonneg hA hB]

end Order

/-! ### Probability -/

section Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

lemma covMat_isSymm {n : ℕ} (X : Ω → Fin n → ℝ) : (covMat X P).IsSymm :=
  IsSymm.ext fun i j ↦ by simp [covMat, covariance_comm]

/-- Second-moment form of the covariance matrix: `Cov[X] = E[X Xᵀ] - E[X] E[X]ᵀ`. -/
lemma covMat_eq_sub [IsProbabilityMeasure P] {n : ℕ} {X : Ω → Fin n → ℝ} (hX : MemLp X 2 P) :
    covMat X P = of (∫ ω, outer (X ω) ∂P) - vecMulVec (∫ ω, X ω ∂P) (∫ ω, X ω ∂P) := by
  have hXi : Integrable X P := hX.integrable one_le_two
  ext i j
  rw [Matrix.sub_apply, of_apply, integral_outer_apply hX, vecMulVec_apply, eval_integral hXi.eval,
    eval_integral hXi.eval, covMat, of_apply, covariance_eq_sub (hX.eval i) (hX.eval j)]
  rfl

/-- Koja's cross-product covariance theorem with non-zero means: for independent square-integrable
`X` and `Y` with means `m` and `m'`,
`Cov[X ⨯ Y] = (Cov[X] + m mᵀ) ⊠ (Cov[Y] + m' m'ᵀ) - (m mᵀ) ⊠ (m' m'ᵀ)`. -/
theorem covMat_cross_of_mean [IsProbabilityMeasure P] {X Y : Ω → Fin 3 → ℝ}
    (hXY : X ⟂ᵢ[P] Y) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) {m m' : Fin 3 → ℝ}
    (hm : ∫ ω, X ω ∂P = m) (hm' : ∫ ω, Y ω ∂P = m') :
    covMat (fun ω ↦ X ω ⨯₃ Y ω) P
      = (covMat X P + vecMulVec m m) ⊠ (covMat Y P + vecMulVec m' m')
        - vecMulVec m m ⊠ vecMulVec m' m' := by
  have hXi : Integrable X P := hX.integrable one_le_two
  have hYi : Integrable Y P := hY.integrable one_le_two
  let crossL := (crossProduct (R := ℝ)).toContinuousBilinearMap
  have hmean : ∫ ω, X ω ⨯₃ Y ω ∂P = m ⨯₃ m' := by
    have := hXY.integral_bilin hXi hYi crossL
    simp only [crossL, LinearMap.toContinuousBilinearMap_apply] at this
    rw [this, hm, hm']
  have hOXY : (fun ω ↦ outer (X ω)) ⟂ᵢ[P] (fun ω ↦ outer (Y ω)) :=
    hXY.comp (φ := outer) (ψ := outer) (by fun_prop) (by fun_prop)
  have hF := hOXY.integral_bilin (integrable_outer hX) (integrable_outer hY) boxTimesL
  rw [covMat_eq_sub (memLp_cross hXY hX hY), covMat_eq_sub hX, covMat_eq_sub hY, hm, hm',
    hmean, sub_add_cancel, sub_add_cancel, ← boxTimes_vecMulVec]
  congr 1
  simp_rw [outer_cross]
  rw [hF, boxTimesL_apply]
  rfl

/-- Koja's isotropic-noise corollary: if `Cov[Y] = σ² 1`, then
`Cov[X ⨯ Y] = σ² (tr(Cov[X]) 1 - Cov[X])`. -/
theorem covMat_cross_isotropic [IsProbabilityMeasure P] {X Y : Ω → Fin 3 → ℝ}
    (hXY : X ⟂ᵢ[P] Y) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX0 : ∀ i, ∫ ω, X ω i ∂P = 0) (hY0 : ∀ i, ∫ ω, Y ω i ∂P = 0) {σ2 : ℝ}
    (hσ : covMat Y P = σ2 • 1) :
    covMat (fun ω ↦ X ω ⨯₃ Y ω) P = σ2 • ((covMat X P).trace • 1 - covMat X P) := by
  rw [covMat_cross hXY hX hY hX0 hY0, hσ, boxTimes_smul_right, boxTimes_comm,
    one_boxTimes (covMat_isSymm X)]

end Probability

end Koja
