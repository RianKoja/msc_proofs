/-
Copyright (c) 2026 Rian Koja. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rian Koja
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Koja's trend line for the `v` vectors

Closed form for the norm of the integrated gravity vector seen from a frame rotating with the
Earth, for a stationary vehicle.
-/
namespace Koja

open Real Matrix

/-- Rotation by angle `θ` about the third axis. -/
noncomputable def rotZ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0; sin θ, cos θ, 0; 0, 0, 1]

lemma integral_rotZ_mulVec (φ ω t : ℝ) (hω : ω ≠ 0) :
    ∫ τ in (0)..t, rotZ (ω * τ) *ᵥ ![cos φ, 0, -sin φ]
      = ![cos φ * sin (ω * t) / ω, cos φ * (1 - cos (ω * t)) / ω, -sin φ * t] := by
  have hF : (fun τ ↦ rotZ (ω * τ) *ᵥ ![cos φ, 0, -sin φ])
      = fun τ ↦ ![cos φ * cos (ω * τ), cos φ * sin (ω * τ), -sin φ] := by
    ext τ i
    fin_cases i <;>
      simp only [mulVec, dotProduct, rotZ, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        of_apply, cons_val', cons_val_fin_one, cons_val_zero, cons_val_one, cons_val,
        Fin.sum_univ_three, mul_zero, add_zero, zero_add, mul_neg, zero_mul, neg_zero, one_mul] <;>
      ring
  have hc : Continuous fun τ : ℝ ↦ ![cos φ * cos (ω * τ), cos φ * sin (ω * τ), -sin φ] := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      cons_val_zero, cons_val_one, cons_val] <;> fun_prop
  rw [hF]
  ext i
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) i).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
  simp only [ContinuousLinearMap.proj_apply] at this
  rw [← this]
  fin_cases i
  · simp [intervalIntegral.integral_comp_mul_left (fun x ↦ cos x) hω, integral_cos]
    field_simp
  · simp [intervalIntegral.integral_comp_mul_left (fun x ↦ sin x) hω, integral_sin]
    field_simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul]
    ring

/-- Koja's trend line for the `v` vectors: for a stationary vehicle at latitude `φ`, with gravity
`g₀` and Earth rate `ω`, the norm of the integrated rotated gravity vector after time `t` is
`g₀ t √(sin² φ + cos² φ sinc²(ω t / 2))`. Mathlib's `sinc x = sin x / x` is unnormalized, so
`sinc (ω t / 2)` here is the thesis's normalized `sinc (ω t / 2π)`. -/
theorem trendLine (g₀ φ ω t : ℝ) (hg : 0 ≤ g₀) (ht : 0 ≤ t) (hω : ω ≠ 0) :
    ‖WithLp.toLp 2 (g₀ • ∫ τ in (0)..t, rotZ (ω * τ) *ᵥ ![cos φ, 0, -sin φ])‖
      = g₀ * t * √(sin φ ^ 2 + cos φ ^ 2 * sinc (ω * t / 2) ^ 2) := by
  rw [integral_rotZ_mulVec φ ω t hω, EuclideanSpace.norm_eq]
  rcases ht.eq_or_lt with rfl | ht
  · simp [Fin.sum_univ_three]
  have hx : ω * t / 2 ≠ 0 := by positivity
  rw [sinc_of_ne_zero hx, ← Real.sqrt_sq (by positivity : 0 ≤ g₀ * t), ← Real.sqrt_mul
    (by positivity)]
  congr 1
  simp only [neg_mul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_eq_abs, mul_pow, sq_abs,
    Fin.sum_univ_three, Fin.isValue, cons_val_zero, cons_val_one, cons_val, even_two, Even.neg_pow]
  set a := ω * t / 2
  have e : ω * t = 2 * a := by ring
  have h := sin_sq_add_cos_sq a
  rw [e, sin_two_mul, cos_two_mul]
  have hω' : ω = 2 * a / t := by
    rw [eq_div_iff ht.ne']
    exact e
  rw [hω']
  field_simp
  linear_combination g₀ ^ 2 * cos φ ^ 2 * (4 * cos a ^ 2 - 4) * h

end Koja
