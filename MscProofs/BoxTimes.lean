/-
Copyright (c) 2026 Rian Koja. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rian Koja
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Koja's box-times operator

For independent zero-mean random vectors `μ ε : ℝ³` with covariances `A` and `B`,
the covariance of `μ ⨯₃ ε` depends only on `A` and `B`. Koja's box-times operator
`A ⊠ B` is that covariance, given entrywise by an explicit bilinear formula.

This file proves the algebraic core:
* `Koja.boxTimes_vecMulVec` (Koja's identity): for rank-one arguments,
  `(u uᵀ) ⊠ (v vᵀ) = (u ⨯₃ v)(u ⨯₃ v)ᵀ`;
* `Koja.boxTimes_comm`: Koja's commutativity property;
* `Koja.boxTimes_smul_left`, `Koja.boxTimes_smul_right`: Koja's scaling properties;
* `Koja.boxTimesₗ`: Koja's bilinearity property, packaging `⊠` as a bilinear map.
-/

namespace Koja

open Matrix

variable {R : Type*} [CommRing R]

/-- Koja's box-times operator on `3 × 3` matrices. Only the upper triangle of each argument
is read, so it is intended for symmetric (covariance) matrices. -/
def boxTimes (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  let m00 := A 2 2 * B 1 1 - 2 * A 1 2 * B 1 2 + A 1 1 * B 2 2
  let m01 := -A 2 2 * B 0 1 + A 1 2 * B 0 2 + A 0 2 * B 1 2 - A 0 1 * B 2 2
  let m02 := A 1 2 * B 0 1 - A 1 1 * B 0 2 - A 0 2 * B 1 1 + A 0 1 * B 1 2
  let m11 := A 2 2 * B 0 0 - 2 * A 0 2 * B 0 2 + A 0 0 * B 2 2
  let m12 := -A 1 2 * B 0 0 + A 0 2 * B 0 1 + A 0 1 * B 0 2 - A 0 0 * B 1 2
  let m22 := A 1 1 * B 0 0 - 2 * A 0 1 * B 0 1 + A 0 0 * B 1 1
  !![m00, m01, m02; m01, m11, m12; m02, m12, m22]

@[inherit_doc] scoped infixl:70 " ⊠ " => boxTimes

/-- Koja's identity: on rank-one (outer product) arguments, the box-times operator is the
outer product of the cross product with itself. -/
theorem boxTimes_vecMulVec (u v : Fin 3 → R) :
    vecMulVec u u ⊠ vecMulVec v v = vecMulVec (u ⨯₃ v) (u ⨯₃ v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boxTimes, vecMulVec_apply, cross_apply] <;> ring

/-- Koja's commutativity property of the box-times operator. -/
theorem boxTimes_comm (A B : Matrix (Fin 3) (Fin 3) R) : A ⊠ B = B ⊠ A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boxTimes] <;> ring

/-- Koja's scaling property in the left argument. -/
theorem boxTimes_smul_left (c : R) (A B : Matrix (Fin 3) (Fin 3) R) :
    (c • A) ⊠ B = c • (A ⊠ B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boxTimes] <;> ring

/-- Koja's additivity property in the left argument. -/
theorem boxTimes_add_left (A A' B : Matrix (Fin 3) (Fin 3) R) :
    (A + A') ⊠ B = A ⊠ B + A' ⊠ B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boxTimes] <;> ring

/-- Koja's additivity property in the right argument. -/
theorem boxTimes_add_right (A B B' : Matrix (Fin 3) (Fin 3) R) :
    A ⊠ (B + B') = A ⊠ B + A ⊠ B' := by
  rw [boxTimes_comm, boxTimes_add_left, boxTimes_comm, boxTimes_comm B']

/-- Koja's scaling property in the right argument. -/
theorem boxTimes_smul_right (c : R) (A B : Matrix (Fin 3) (Fin 3) R) :
    A ⊠ (c • B) = c • (A ⊠ B) := by
  rw [boxTimes_comm, boxTimes_smul_left, boxTimes_comm]

/-- Koja's scaling property: scaling the vectors by `a` and `b` scales the covariance of their
cross product by `a² b²`. -/
theorem boxTimes_smul_smul (a b : R) (A B : Matrix (Fin 3) (Fin 3) R) :
    (a ^ 2 • A) ⊠ (b ^ 2 • B) = (a ^ 2 * b ^ 2) • (A ⊠ B) := by
  rw [boxTimes_smul_left, boxTimes_smul_right, smul_smul]

/-- Koja's bilinearity property: the box-times operator as a bilinear map. -/
def boxTimesₗ : Matrix (Fin 3) (Fin 3) R →ₗ[R] Matrix (Fin 3) (Fin 3) R →ₗ[R]
    Matrix (Fin 3) (Fin 3) R :=
  LinearMap.mk₂ R boxTimes boxTimes_add_left boxTimes_smul_left boxTimes_add_right
    boxTimes_smul_right

@[simp]
theorem boxTimesₗ_apply (A B : Matrix (Fin 3) (Fin 3) R) : boxTimesₗ A B = A ⊠ B := rfl

end Koja
