/-
Copyright (c) 2026 Rian Koja. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rian Koja
-/
import MscProofs.Covariance
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Koja's multivariate Chebyshev inequality

`P[‖X - E X‖ ≥ k √(tr K)] ≤ 1 / k²` for a square-integrable random vector `X` with covariance
matrix `K`, provided `tr K > 0`.
-/
namespace Koja

open MeasureTheory ProbabilityTheory Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {n : ℕ}

/-- The expected squared Euclidean deviation of a random vector from its mean is the trace of its
covariance matrix. -/
lemma integrable_sq_sub_mean [IsFiniteMeasure P] {X : Ω → Fin n → ℝ} (hX : MemLp X 2 P)
    (i : Fin n) : Integrable (fun ω ↦ (X ω i - ∫ ω', X ω' i ∂P) ^ 2) P :=
  ((hX.eval i).sub (memLp_const _)).integrable_sq

lemma integral_sum_sq_sub_mean [IsFiniteMeasure P] {X : Ω → Fin n → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, ∑ i, (X ω i - ∫ ω', X ω' i ∂P) ^ 2 ∂P = (covMat X P).trace := by
  rw [integral_finsetSum _ fun i _ ↦ integrable_sq_sub_mean hX i]
  simp [trace, covMat, covariance, sq]

/-- Koja's multivariate Chebyshev inequality: a random vector deviates from its mean by at least
`k √(tr K)` in Euclidean norm with probability at most `1 / k²`, where `K` is its covariance
matrix. The hypothesis `0 < tr K` is necessary: for a constant vector and `k > 1` the event is
certain. -/
theorem chebyshev_multivariate [IsProbabilityMeasure P] {X : Ω → Fin n → ℝ} (hX : MemLp X 2 P)
    {k : ℝ} (hk : 0 < k) (htr : 0 < (covMat X P).trace) :
    P.real {ω | k * √(covMat X P).trace ≤
      ‖WithLp.toLp 2 (X ω - fun i ↦ ∫ ω', X ω' i ∂P)‖} ≤ 1 / k ^ 2 := by
  set t := (covMat X P).trace
  set f : Ω → ℝ := fun ω ↦ ∑ i, (X ω i - ∫ ω', X ω' i ∂P) ^ 2
  have hset : {ω | k * √t ≤ ‖WithLp.toLp 2 (X ω - fun i ↦ ∫ ω', X ω' i ∂P)‖}
      = {ω | k ^ 2 * t ≤ f ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, EuclideanSpace.norm_eq, f]
    rw [Real.le_sqrt (by positivity) (Finset.sum_nonneg fun _ _ ↦ by positivity), mul_pow,
      Real.sq_sqrt htr.le]
    simp
  have hf : Integrable f P :=
    integrable_finsetSum _ fun i _ ↦ integrable_sq_sub_mean hX i
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ by positivity) hf (k ^ 2 * t)
  rw [integral_sum_sq_sub_mean hX] at hm
  rw [hset, le_div_iff₀ (by positivity)]
  nlinarith

/-- The positivity hypothesis in `chebyshev_multivariate` cannot be dropped: for a constant random
vector the deviation event is certain, while `1 / k² < 1` for `k > 1`. -/
theorem chebyshev_multivariate_const [IsProbabilityMeasure P] (k : ℝ) :
    P.real {_ω | k * √(covMat (fun _ : Ω ↦ (0 : Fin n → ℝ)) P).trace ≤
      ‖WithLp.toLp 2 ((0 : Fin n → ℝ) - fun _ ↦ ∫ _, (0 : ℝ) ∂P)‖} = 1 := by
  have h1 : covMat (fun _ : Ω ↦ (0 : Fin n → ℝ)) P = 0 := by
    ext
    simp [covMat, covariance]
  simp [h1]

end Koja
