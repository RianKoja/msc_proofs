/-
Copyright (c) 2026 Rian Koja. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rian Koja
-/
import MscProofs.BoxTimes
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Koja's cross-product covariance theorem

For independent zero-mean square-integrable random vectors `X Y : Ω → ℝ³`,
`Cov[X ⨯ Y] = Cov[X] ⊠ Cov[Y]`, where `⊠` is Koja's box-times operator.

* `Koja.covMat_cross`: Koja's cross-product covariance theorem;
* `Koja.covMat_smul_cross`: Koja's scaling property, `Cov[aX ⨯ bY] = a² b² (Cov[X] ⊠ Cov[Y])`;
* `Koja.covMat_cross_mulVec`: Koja's pre-multiplication property of the second vector;
* `Koja.covMat_mulVec_cross`: Koja's pre-multiplication property on `⊠`.
-/
namespace Koja

open MeasureTheory ProbabilityTheory Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {n : ℕ}

/-- The covariance matrix of a random vector. -/
noncomputable def covMat (X : Ω → Fin n → ℝ) (P : Measure Ω) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P]

/-- Outer product `x xᵀ`, as a plain function so that it carries the sup norm. -/
def outer (x : Fin n → ℝ) : Fin n → Fin n → ℝ := fun i j ↦ x i * x j

@[fun_prop]
lemma measurable_outer : Measurable (outer : (Fin n → ℝ) → Fin n → Fin n → ℝ) := by
  unfold outer
  fun_prop

lemma integrable_outer {X : Ω → Fin n → ℝ} (hX : MemLp X 2 P) :
    Integrable (fun ω ↦ outer (X ω)) P :=
  Integrable.of_eval fun i ↦ Integrable.of_eval fun j ↦
    (hX.eval i).integrable_mul (hX.eval j)

lemma integral_outer_apply {X : Ω → Fin n → ℝ} (hX : MemLp X 2 P)
    (i j : Fin n) : (∫ ω, outer (X ω) ∂P) i j = ∫ ω, X ω i * X ω j ∂P := by
  rw [eval_integral (Integrable.eval (integrable_outer hX)),
    eval_integral fun j ↦ (Integrable.eval (integrable_outer hX) i).eval j]
  rfl

/-- Koja's box-times operator as a continuous bilinear map on plain `3 × 3` arrays. -/
noncomputable def boxTimesL :
    (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  let e : (Fin 3 → Fin 3 → ℝ) ≃ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ := ofLinearEquiv ℝ
  ((boxTimesₗ.compl₁₂ e.toLinearMap e.toLinearMap).compr₂
    e.symm.toLinearMap).toContinuousBilinearMap

lemma boxTimesL_apply (A B : Fin 3 → Fin 3 → ℝ) : boxTimesL A B = of.symm (of A ⊠ of B) := rfl

lemma outer_cross (u v : Fin 3 → ℝ) :
    outer (u ⨯₃ v) = boxTimesL (outer u) (outer v) := by
  have hu : of (outer u) = vecMulVec u u := rfl
  have hv : of (outer v) = vecMulVec v v := rfl
  rw [boxTimesL_apply, hu, hv, boxTimes_vecMulVec]
  rfl

lemma integral_eq_zero_of_eval {X : Ω → Fin n → ℝ} (hX : Integrable X P)
    (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) : ∫ ω, X ω ∂P = 0 := by
  ext i
  rw [eval_integral hX.eval, h0, Pi.zero_apply]

/-- Koja's cross-product covariance theorem: for independent zero-mean square-integrable random
vectors `X` and `Y` in `ℝ³`, the covariance of `X ⨯₃ Y` is `covMat X ⊠ covMat Y`. -/
theorem covMat_cross [IsProbabilityMeasure P] {X Y : Ω → Fin 3 → ℝ}
    (hXY : X ⟂ᵢ[P] Y) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX0 : ∀ i, ∫ ω, X ω i ∂P = 0) (hY0 : ∀ i, ∫ ω, Y ω i ∂P = 0) :
    covMat (fun ω ↦ X ω ⨯₃ Y ω) P = covMat X P ⊠ covMat Y P := by
  have hXi : Integrable X P := hX.integrable one_le_two
  have hYi : Integrable Y P := hY.integrable one_le_two
  let crossL := (crossProduct (R := ℝ)).toContinuousBilinearMap
  -- The cross product has zero mean.
  have hZi : Integrable (fun ω ↦ X ω ⨯₃ Y ω) P := hXY.integrable_bilin hXi hYi crossL
  have hZ0 : ∀ i, ∫ ω, (X ω ⨯₃ Y ω) i ∂P = 0 := by
    intro i
    have h : ∫ ω, X ω ⨯₃ Y ω ∂P = 0 := by
      have := hXY.integral_bilin hXi hYi crossL
      simp only [crossL, LinearMap.toContinuousBilinearMap_apply] at this
      rw [this, integral_eq_zero_of_eval hXi hX0, map_zero, LinearMap.zero_apply]
    rw [← eval_integral hZi.eval, h, Pi.zero_apply]
  -- Second moments factor through Koja's identity and independence.
  have hOXY : (fun ω ↦ outer (X ω)) ⟂ᵢ[P] (fun ω ↦ outer (Y ω)) :=
    hXY.comp (φ := outer) (ψ := outer) (by fun_prop) (by fun_prop)
  have hF := hOXY.integral_bilin (integrable_outer hX) (integrable_outer hY) boxTimesL
  have hFi := hOXY.integrable_bilin (integrable_outer hX) (integrable_outer hY) boxTimesL
  ext i j
  have lhs : covMat (fun ω ↦ X ω ⨯₃ Y ω) P i j
      = (∫ ω, boxTimesL (outer (X ω)) (outer (Y ω)) ∂P) i j := by
    rw [eval_integral hFi.eval, eval_integral fun j ↦ (hFi.eval i).eval j]
    simp [covMat, covariance, hZ0, ← outer_cross, outer]
  have hc : ∀ {Z : Ω → Fin 3 → ℝ}, MemLp Z 2 P → (∀ i, ∫ ω, Z ω i ∂P = 0) →
      covMat Z P = of (∫ ω, outer (Z ω) ∂P) := by
    intro Z hZ h0
    ext a b
    simp [covMat, covariance, h0, integral_outer_apply hZ]
  rw [lhs, hF, hc hX hX0, hc hY hY0, boxTimesL_apply]
  rfl

/-- Scaling a random vector by `c` scales its covariance matrix by `c²`. -/
lemma covMat_smul (c : ℝ) (Z : Ω → Fin n → ℝ) :
    covMat (fun ω ↦ c • Z ω) P = c ^ 2 • covMat Z P := by
  ext i j
  simp [covMat, covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- Koja's scaling property for the covariance of a cross product: scaling the vectors by `a`
and `b` scales the covariance of their cross product by `a² b²`. -/
theorem covMat_smul_cross [IsProbabilityMeasure P] {X Y : Ω → Fin 3 → ℝ}
    (hXY : X ⟂ᵢ[P] Y) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX0 : ∀ i, ∫ ω, X ω i ∂P = 0) (hY0 : ∀ i, ∫ ω, Y ω i ∂P = 0) (a b : ℝ) :
    covMat (fun ω ↦ (a • X ω) ⨯₃ (b • Y ω)) P = (a ^ 2 * b ^ 2) • (covMat X P ⊠ covMat Y P) := by
  have h : (fun ω ↦ (a • X ω) ⨯₃ (b • Y ω)) = fun ω ↦ (a * b) • (X ω ⨯₃ Y ω) := by
    ext ω : 1
    simp [smul_smul, mul_comm]
  rw [h, covMat_smul, covMat_cross hXY hX hY hX0 hY0, mul_pow]

/-- Covariance of a linear transformation: `Cov[D Z] = D Cov[Z] Dᵀ`. -/
theorem covMat_mulVec (D : Matrix (Fin n) (Fin n) ℝ) {Z : Ω → Fin n → ℝ} (hZ : MemLp Z 2 P)
    [IsFiniteMeasure P] :
    covMat (fun ω ↦ D *ᵥ Z ω) P = D * covMat Z P * Dᵀ := by
  ext i j
  have hZ' : ∀ (r : Fin n → ℝ) k, MemLp (fun ω ↦ r k * Z ω k) 2 P := fun r k ↦
    (hZ.eval k).const_mul (r k)
  simp only [covMat, of_apply, mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum (fun k ↦ hZ' (D i) k) (fun k ↦ hZ' (D j) k)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, mul_apply, transpose_apply,
    of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- Koja's pre-multiplication property: `Cov[X ⨯ (C Y)] = Cov[X] ⊠ (C Cov[Y] Cᵀ)`. -/
theorem covMat_cross_mulVec [IsProbabilityMeasure P] {X Y : Ω → Fin 3 → ℝ}
    (hXY : X ⟂ᵢ[P] Y) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX0 : ∀ i, ∫ ω, X ω i ∂P = 0) (hY0 : ∀ i, ∫ ω, Y ω i ∂P = 0)
    (C : Matrix (Fin 3) (Fin 3) ℝ) :
    covMat (fun ω ↦ X ω ⨯₃ (C *ᵥ Y ω)) P = covMat X P ⊠ (C * covMat Y P * Cᵀ) := by
  have hCY : MemLp (fun ω ↦ C *ᵥ Y ω) 2 P :=
    (Matrix.mulVecLin C).toContinuousLinearMap.comp_memLp' hY
  have hCY0 : ∀ i, ∫ ω, (C *ᵥ Y ω) i ∂P = 0 := by
    intro i
    simp only [mulVec, dotProduct]
    rw [integral_finsetSum _ fun k _ ↦ ((hY.eval k).integrable one_le_two).const_mul (C i k)]
    simp [integral_const_mul, hY0]
  have h : covMat (fun ω ↦ X ω ⨯₃ (C *ᵥ Y ω)) P = covMat X P ⊠ covMat (fun ω ↦ C *ᵥ Y ω) P :=
    covMat_cross (hXY.comp measurable_id
    (Matrix.mulVecLin C).toContinuousLinearMap.continuous.measurable) hX hCY hX0 hCY0
  rw [h, covMat_mulVec C hY]

/-- The product of independent square-integrable random variables is square-integrable. -/
lemma memLp_two_mul_of_indepFun {f g : Ω → ℝ} (h : f ⟂ᵢ[P] g) (hf : MemLp f 2 P)
    (hg : MemLp g 2 P) : MemLp (fun ω ↦ f ω * g ω) 2 P := by
  change MemLp (f * g) 2 P
  rw [memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)]
  have := (h.comp (φ := fun x ↦ x ^ 2) (ψ := fun x ↦ x ^ 2) (by fun_prop)
    (by fun_prop)).integrable_mul hf.integrable_sq hg.integrable_sq
  convert this using 1
  ext ω
  simp [mul_pow]

/-- The cross product of independent square-integrable random vectors is square-integrable. -/
lemma memLp_cross {X Y : Ω → Fin 3 → ℝ} (hXY : X ⟂ᵢ[P] Y) (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) : MemLp (fun ω ↦ X ω ⨯₃ Y ω) 2 P := by
  have hm : ∀ a b, MemLp (fun ω ↦ X ω a * Y ω b) 2 P := fun a b ↦
    memLp_two_mul_of_indepFun (hXY.comp (measurable_pi_apply a) (measurable_pi_apply b))
      (hX.eval a) (hY.eval b)
  refine MemLp.of_eval fun i ↦ ?_
  fin_cases i <;> simp only [cross_apply] <;> exact (hm _ _).sub (hm _ _)

/-- Koja's pre-multiplication property on `⊠`: `Cov[D (X ⨯ Y)] = D (Cov[X] ⊠ Cov[Y]) Dᵀ`. -/
theorem covMat_mulVec_cross [IsProbabilityMeasure P] {X Y : Ω → Fin 3 → ℝ}
    (hXY : X ⟂ᵢ[P] Y) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX0 : ∀ i, ∫ ω, X ω i ∂P = 0) (hY0 : ∀ i, ∫ ω, Y ω i ∂P = 0)
    (D : Matrix (Fin 3) (Fin 3) ℝ) :
    covMat (fun ω ↦ D *ᵥ (X ω ⨯₃ Y ω)) P = D * (covMat X P ⊠ covMat Y P) * Dᵀ := by
  rw [covMat_mulVec D (memLp_cross hXY hX hY), covMat_cross hXY hX hY hX0 hY0]

end Koja
