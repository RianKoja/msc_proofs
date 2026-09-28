/-
Copyright (c) 2026 Rian Koja. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rian Koja
-/
import MscProofs.Covariance

/-!
# Koja's covariance propagation

Case 1 of the covariance propagation results: the covariance of a sum of known gains times
pairwise independent noise, in closed form and as a one-step recursion.
-/
namespace Koja

open MeasureTheory ProbabilityTheory Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {n : ℕ}

/-- The covariance matrix of a sum of pairwise independent random vectors is the sum of their
covariance matrices. -/
theorem covMat_sum [IsFiniteMeasure P] {ι : Type*} (s : Finset ι) {Z : ι → Ω → Fin n → ℝ}
    (hZ : ∀ k, MemLp (Z k) 2 P) (hind : Pairwise fun k j ↦ Z k ⟂ᵢ[P] Z j) :
    covMat (fun ω ↦ ∑ k ∈ s, Z k ω) P = ∑ k ∈ s, covMat (Z k) P := by
  classical
  ext a b
  simp only [covMat, of_apply, Finset.sum_apply, Matrix.sum_apply]
  rw [covariance_fun_sum_fun_sum' (fun k _ ↦ (hZ k).eval a) (fun k _ ↦ (hZ k).eval b)]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.sum_eq_single_of_mem k hk fun j _ hjk ↦ ?_]
  exact ((hind hjk.symm).comp (measurable_pi_apply a) (measurable_pi_apply b)).covariance_eq_zero
    ((hZ k).eval a) ((hZ j).eval b)

/-- Koja's covariance propagation, case 1 (sum of known gains times noise): for pairwise
independent noise vectors `ε k` sharing the covariance `K`,
`Cov[∑ f k ε k] = ∑ f k K (f k)ᵀ`. -/
theorem covMat_sum_mulVec [IsFiniteMeasure P] (s : Finset ℕ) (f : ℕ → Matrix (Fin n) (Fin n) ℝ)
    {ε : ℕ → Ω → Fin n → ℝ} (hε : ∀ k, MemLp (ε k) 2 P)
    (hind : Pairwise fun k j ↦ ε k ⟂ᵢ[P] ε j) {K : Matrix (Fin n) (Fin n) ℝ}
    (hK : ∀ k, covMat (ε k) P = K) :
    covMat (fun ω ↦ ∑ k ∈ s, f k *ᵥ ε k ω) P = ∑ k ∈ s, f k * K * (f k)ᵀ := by
  have hm : ∀ k, MemLp (fun ω ↦ f k *ᵥ ε k ω) 2 P := fun k ↦
    (Matrix.mulVecLin (f k)).toContinuousLinearMap.comp_memLp' (hε k)
  rw [covMat_sum s hm fun k j hkj ↦ (hind hkj).comp
    (Matrix.mulVecLin (f k)).toContinuousLinearMap.continuous.measurable
    (Matrix.mulVecLin (f j)).toContinuousLinearMap.continuous.measurable]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [covMat_mulVec (f k) (hε k), hK]

/-- Recursive form of Koja's case 1: the covariance after `m + 1` steps is the covariance after
`m` steps plus `f m K (f m)ᵀ`, so it can be propagated with a single matrix of state. -/
theorem covMat_sum_mulVec_succ [IsFiniteMeasure P] (m : ℕ) (f : ℕ → Matrix (Fin n) (Fin n) ℝ)
    {ε : ℕ → Ω → Fin n → ℝ} (hε : ∀ k, MemLp (ε k) 2 P)
    (hind : Pairwise fun k j ↦ ε k ⟂ᵢ[P] ε j) {K : Matrix (Fin n) (Fin n) ℝ}
    (hK : ∀ k, covMat (ε k) P = K) :
    covMat (fun ω ↦ ∑ k ∈ Finset.range (m + 1), f k *ᵥ ε k ω) P
      = covMat (fun ω ↦ ∑ k ∈ Finset.range m, f k *ᵥ ε k ω) P + f m * K * (f m)ᵀ := by
  rw [covMat_sum_mulVec _ f hε hind hK, covMat_sum_mulVec _ f hε hind hK,
    Finset.sum_range_succ]

end Koja
