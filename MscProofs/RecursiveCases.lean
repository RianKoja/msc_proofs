/-
Copyright (c) 2026 Rian Koja. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rian Koja
-/
import MscProofs.CovariancePropagation

/-!
# Koja's covariance propagation, cases 2 to 4

* `Koja.covMat_case2`: Koja's case 2, a sum of known gains times the cross product of a bias with
  a case 1 sum;
* `Koja.covMat_case3`: Koja's case 3, the same with a fresh noise at each step instead of a bias;
* `Koja.covMat_case4`: Koja's case 4, a sum of known gains times a case 1 sum.
-/
namespace Koja

open MeasureTheory ProbabilityTheory Matrix Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Uncorrelated sums -/

section Uncorrelated

variable {n : ℕ}

lemma memLp_mulVec (D : Matrix (Fin n) (Fin n) ℝ) {Z : Ω → Fin n → ℝ} (hZ : MemLp Z 2 P) :
    MemLp (fun ω ↦ D *ᵥ Z ω) 2 P :=
  (Matrix.mulVecLin D).toContinuousLinearMap.comp_memLp' hZ

lemma integral_mulVec_eq_zero (D : Matrix (Fin n) (Fin n) ℝ) {Z : Ω → Fin n → ℝ}
    (hZ : MemLp Z 2 P) [IsFiniteMeasure P] (hZ0 : ∀ i, ∫ ω, Z ω i ∂P = 0) (i : Fin n) :
    ∫ ω, (D *ᵥ Z ω) i ∂P = 0 := by
  simp only [mulVec, dotProduct]
  rw [integral_finsetSum _ fun k _ ↦ ((hZ.eval k).integrable one_le_two).const_mul (D i k)]
  simp [integral_const_mul, hZ0]

/-- Linear maps preserve uncorrelation. -/
lemma covariance_mulVec_eq_zero [IsFiniteMeasure P] (D E : Matrix (Fin n) (Fin n) ℝ)
    {Z Y : Ω → Fin n → ℝ} (hZ : MemLp Z 2 P) (hY : MemLp Y 2 P)
    (h : ∀ k l, cov[fun ω ↦ Z ω k, fun ω ↦ Y ω l; P] = 0) (a b : Fin n) :
    cov[fun ω ↦ (D *ᵥ Z ω) a, fun ω ↦ (E *ᵥ Y ω) b; P] = 0 := by
  simp only [mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum (fun k ↦ (hZ.eval k).const_mul (D a k))
    (fun l ↦ (hY.eval l).const_mul (E b l))]
  simp [covariance_const_mul_left, covariance_const_mul_right, h]

/-- The covariance matrix of a sum of pairwise uncorrelated random vectors, each premultiplied by
a known matrix, is `∑ D k Cov[Z k] (D k)ᵀ`. -/
theorem covMat_sum_mulVec_of_uncorrelated [IsFiniteMeasure P] {ι : Type*} (s : Finset ι)
    (D : ι → Matrix (Fin n) (Fin n) ℝ) {Z : ι → Ω → Fin n → ℝ} (hZ : ∀ k, MemLp (Z k) 2 P)
    (hunc : ∀ k j, k ≠ j → ∀ a b, cov[fun ω ↦ Z k ω a, fun ω ↦ Z j ω b; P] = 0) :
    covMat (fun ω ↦ ∑ k ∈ s, D k *ᵥ Z k ω) P = ∑ k ∈ s, D k * covMat (Z k) P * (D k)ᵀ := by
  classical
  have hm : ∀ k, MemLp (fun ω ↦ D k *ᵥ Z k ω) 2 P := fun k ↦ memLp_mulVec (D k) (hZ k)
  have hsum : covMat (fun ω ↦ ∑ k ∈ s, D k *ᵥ Z k ω) P
      = ∑ k ∈ s, covMat (fun ω ↦ D k *ᵥ Z k ω) P := by
    ext a b
    simp only [covMat, of_apply, Finset.sum_apply, Matrix.sum_apply]
    rw [covariance_fun_sum_fun_sum' (fun k _ ↦ (hm k).eval a) (fun k _ ↦ (hm k).eval b)]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.sum_eq_single_of_mem k hk fun j _ hjk ↦
      covariance_mulVec_eq_zero _ _ (hZ k) (hZ j) (hunc k j hjk.symm) a b]
  rw [hsum]
  exact Finset.sum_congr rfl fun k _ ↦ covMat_mulVec (D k) (hZ k)

lemma covMat_transpose (Z : Ω → Fin n → ℝ) : (covMat Z P)ᵀ = covMat Z P := by
  ext i j
  simp [covMat, covariance_comm]

end Uncorrelated

/-! ### Cross products with an independent zero-mean factor -/

section Cross

lemma integral_mul_cross_eq_zero [IsProbabilityMeasure P] {V U : Ω → Fin 3 → ℝ} {W : Ω → ℝ}
    (hind : V ⟂ᵢ[P] fun ω ↦ (W ω, U ω)) (hV : MemLp V 2 P) (hW : MemLp W 2 P)
    (hU : MemLp U 2 P) (hV0 : ∀ i, ∫ ω, V ω i ∂P = 0) (p : Fin 3) :
    ∫ ω, W ω * (V ω ⨯₃ U ω) p ∂P = 0 := by
  have key : ∀ a b, Integrable (fun ω ↦ V ω a * (W ω * U ω b)) P ∧
      ∫ ω, V ω a * (W ω * U ω b) ∂P = 0 := by
    intro a b
    have hi : (fun ω ↦ V ω a) ⟂ᵢ[P] fun ω ↦ W ω * U ω b :=
      hind.comp (measurable_pi_apply a)
        (by fun_prop : Measurable fun x : ℝ × (Fin 3 → ℝ) ↦ x.1 * x.2 b)
    have hWU : Integrable (fun ω ↦ W ω * U ω b) P := hW.integrable_mul (hU.eval b)
    refine ⟨hi.integrable_mul ((hV.eval a).integrable one_le_two) hWU, ?_⟩
    have := hi.integral_mul_eq_mul_integral (hV.eval a).aestronglyMeasurable
      hWU.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hV0, zero_mul]
  have h2 : ∀ a b c d, ∫ ω, W ω * (V ω a * U ω b - V ω c * U ω d) ∂P = 0 := by
    intro a b c d
    simp_rw [show ∀ ω, W ω * (V ω a * U ω b - V ω c * U ω d)
      = V ω a * (W ω * U ω b) - V ω c * (W ω * U ω d) from fun ω ↦ by ring]
    rw [integral_sub (key a b).1 (key c d).1, (key a b).2, (key c d).2, sub_self]
  fin_cases p <;> simp only [cross_apply] <;> exact h2 _ _ _ _

/-- If `V` is zero-mean and independent of `(Y, U)`, then every component of `V ⨯ U` is
uncorrelated with `Y`. -/
lemma covariance_cross_eq_zero [IsProbabilityMeasure P] {V U : Ω → Fin 3 → ℝ} {Y : Ω → ℝ}
    (hind : V ⟂ᵢ[P] fun ω ↦ (Y ω, U ω)) (hV : MemLp V 2 P) (hY : MemLp Y 2 P)
    (hU : MemLp U 2 P) (hV0 : ∀ i, ∫ ω, V ω i ∂P = 0) (p : Fin 3) :
    cov[fun ω ↦ (V ω ⨯₃ U ω) p, Y; P] = 0 := by
  have hVU : V ⟂ᵢ[P] U := hind.comp measurable_id measurable_snd
  have h1 := integral_mul_cross_eq_zero (W := fun _ ↦ 1)
    (hind.comp measurable_id (by fun_prop : Measurable fun x : ℝ × (Fin 3 → ℝ) ↦ ((1 : ℝ), x.2)))
    hV (memLp_const 1) hU hV0 p
  simp only [one_mul, Function.comp_apply, id_eq] at h1
  rw [covariance_eq_sub ((memLp_cross hVU hV hU).eval p) hY]
  simp only [Pi.mul_apply]
  rw [h1, zero_mul, sub_zero]
  simpa [mul_comm] using integral_mul_cross_eq_zero hind hV hY hU hV0 p

@[fun_prop]
lemma Measurable.cross {α : Type*} {mα : MeasurableSpace α} {f g : α → Fin 3 → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x ↦ f x ⨯₃ g x := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  fin_cases i <;> simp only [cross_apply] <;> fun_prop

end Cross

/-! ### Independence of a variable from functions of other variables -/

/-- Extension of a family indexed by `T` to all indices, by zero. -/
noncomputable def extendZero {ι : Type*} (T : Finset ι) (g : T → Fin 3 → ℝ) : ι → Fin 3 → ℝ :=
  open scoped Classical in fun x ↦ if h : x ∈ T then g ⟨x, h⟩ else 0

lemma measurable_extendZero {ι : Type*} (T : Finset ι) : Measurable (extendZero T) := by
  classical
  refine measurable_pi_iff.2 fun x ↦ ?_
  by_cases h : x ∈ T <;> simp only [extendZero, h, dite_true, dite_false]
  exacts [measurable_pi_apply _, measurable_const]

/-- In a mutually independent family, `F i` is independent of any measurable function of the
variables indexed by a finite set not containing `i`. -/
lemma iIndepFun.indepFun_of_local {ι γ : Type*} [MeasurableSpace γ] {F : ι → Ω → Fin 3 → ℝ}
    (hF : iIndepFun F P) (hm : ∀ i, AEMeasurable (F i) P) {i : ι} {T : Finset ι} (hi : i ∉ T)
    {Φ : (ι → Fin 3 → ℝ) → γ} (hΦ : Measurable Φ)
    (hloc : ∀ G G' : ι → Fin 3 → ℝ, (∀ j ∈ T, G j = G' j) → Φ G = Φ G') :
    F i ⟂ᵢ[P] fun ω ↦ Φ fun j ↦ F j ω := by
  classical
  have hφ : Measurable fun g : ({i} : Finset ι) → Fin 3 → ℝ ↦ g ⟨i, Finset.mem_singleton_self i⟩ :=
    measurable_pi_apply _
  have h := (hF.indepFun_finset₀ {i} T (Finset.disjoint_singleton_left.2 hi) hm).comp hφ
    (hΦ.comp (measurable_extendZero T))
  have e : (fun ω ↦ Φ fun j ↦ F j ω)
      = (fun g ↦ Φ (extendZero T g)) ∘ fun ω (j : T) ↦ F j ω :=
    funext fun ω ↦ hloc _ _ fun j hj ↦ by simp [extendZero, hj]
  rw [e]
  exact h

/-! ### Summation by parts -/

section Algebra

variable {n : ℕ}

/-- Exchanging the order of summation: `∑ₖ hₖ ∑_{i ≤ k} wᵢ = ∑ᵢ (H m - H i) wᵢ`, where `H` are the
partial sums of `h`. -/
lemma sum_mulVec_partialSum (h : ℕ → Matrix (Fin n) (Fin n) ℝ) (w : ℕ → Fin n → ℝ) (m : ℕ) :
    ∑ k ∈ range m, h k *ᵥ ∑ i ∈ range (k + 1), w i
      = ∑ i ∈ range m, (∑ j ∈ range m, h j - ∑ j ∈ range i, h j) *ᵥ w i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : ∀ i, ∑ j ∈ range (m + 1), h j - ∑ j ∈ range i, h j
        = (∑ j ∈ range m, h j - ∑ j ∈ range i, h j) + h m := fun i ↦ by
      rw [sum_range_succ]; abel
    simp_rw [e, add_mulVec, sum_add_distrib, ← mulVec_sum]
    rw [sum_range_succ (fun k ↦ h k *ᵥ ∑ i ∈ range (k + 1), w i), ih,
      sum_range_succ (fun i ↦ (∑ j ∈ range m, h j - ∑ j ∈ range i, h j) *ᵥ w i), sub_self,
      zero_mulVec, add_zero]

/-- Expansion of `∑ᵢ (H m - H i) Bᵢ (H m - H i)ᵀ` for symmetric `Bᵢ`. -/
lemma sum_sandwich_sub {H B : ℕ → Matrix (Fin n) (Fin n) ℝ} (hB : ∀ i, (B i)ᵀ = B i) (m : ℕ) :
    ∑ i ∈ range m, (H m - H i) * B i * (H m - H i)ᵀ
      = H m * (∑ i ∈ range m, B i) * (H m)ᵀ
        - ((∑ i ∈ range m, H i * B i) * (H m)ᵀ + ((∑ i ∈ range m, H i * B i) * (H m)ᵀ)ᵀ)
        + ∑ i ∈ range m, H i * B i * (H i)ᵀ := by
  have e : ∀ i, (H m - H i) * B i * (H m - H i)ᵀ
      = H m * B i * (H m)ᵀ - (H i * B i * (H m)ᵀ + (H i * B i * (H m)ᵀ)ᵀ)
        + H i * B i * (H i)ᵀ := fun i ↦ by
    simp only [transpose_sub, transpose_mul, transpose_transpose, hB, sub_mul, mul_sub,
      Matrix.mul_assoc]
    abel
  simp only [e, sum_add_distrib, sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, transpose_sum]

/-- One step of the expansion in `sum_sandwich_sub` when the partial sums gain a term. -/
lemma sum_sandwich_succ (h Q : ℕ → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i, (Q i)ᵀ = Q i) (m : ℕ)
    {H : ℕ → Matrix (Fin n) (Fin n) ℝ} (hH : ∀ k, H k = ∑ i ∈ range k, h i) :
    ∑ i ∈ range (m + 1), (H (m + 1) - H i) * Q i * (H (m + 1) - H i)ᵀ
      = h m * (∑ i ∈ range (m + 1), Q i) * (h m)ᵀ
        + (h m * ((∑ i ∈ range m, Q i) * (H m)ᵀ - ∑ i ∈ range m, Q i * (H i)ᵀ)
          + (h m * ((∑ i ∈ range m, Q i) * (H m)ᵀ - ∑ i ∈ range m, Q i * (H i)ᵀ))ᵀ)
        + ∑ i ∈ range m, (H m - H i) * Q i * (H m - H i)ᵀ := by
  have hs : H (m + 1) = H m + h m := by rw [hH, hH, sum_range_succ]
  have e : ∀ i, (H (m + 1) - H i) * Q i * (H (m + 1) - H i)ᵀ
      = h m * Q i * (h m)ᵀ + (h m * (Q i * (H m)ᵀ - Q i * (H i)ᵀ)
        + (h m * (Q i * (H m)ᵀ - Q i * (H i)ᵀ))ᵀ) + (H m - H i) * Q i * (H m - H i)ᵀ :=
    fun i ↦ by
    simp only [hs, transpose_add, transpose_sub, transpose_mul, transpose_transpose, hQ, add_mul,
      mul_add, sub_mul, mul_sub, Matrix.mul_assoc]
    abel
  rw [sum_range_succ, sum_congr rfl fun i _ ↦ e i, hs, add_sub_cancel_left]
  simp only [mul_add, add_mul, mul_sub, sub_mul, transpose_sub, sum_add_distrib,
    sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, transpose_sum, sum_range_succ]
  abel

end Algebra

/-! ### Case 4 -/

section Case4

variable {n : ℕ}

/-- Koja's case 4 in closed form:
`Cov[∑ₖ hₖ ∑_{i ≤ k} fᵢ εᵢ] = ∑ᵢ (H m - H i) fᵢ K fᵢᵀ (H m - H i)ᵀ`,
with `H` the partial sums of `h`. -/
theorem covMat_case4_closed [IsFiniteMeasure P] (m : ℕ) (h f : ℕ → Matrix (Fin n) (Fin n) ℝ)
    {ε : ℕ → Ω → Fin n → ℝ} (hε : ∀ k, MemLp (ε k) 2 P)
    (hind : Pairwise fun k j ↦ ε k ⟂ᵢ[P] ε j) {K : Matrix (Fin n) (Fin n) ℝ}
    (hK : ∀ k, covMat (ε k) P = K) {H : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ k, H k = ∑ i ∈ range k, h i) :
    covMat (fun ω ↦ ∑ k ∈ range m, h k *ᵥ ∑ i ∈ range (k + 1), f i *ᵥ ε i ω) P
      = ∑ i ∈ range m, (H m - H i) * (f i * K * (f i)ᵀ) * (H m - H i)ᵀ := by
  simp_rw [sum_mulVec_partialSum, ← hH]
  rw [covMat_sum_mulVec_of_uncorrelated _ _ (fun k ↦ memLp_mulVec (f k) (hε k))
    fun k j hkj a b ↦ ((hind hkj).comp (φ := fun v ↦ (f k *ᵥ v) a) (ψ := fun v ↦ (f j *ᵥ v) b)
      (by fun_prop) (by fun_prop)).covariance_eq_zero
      ((memLp_mulVec (f k) (hε k)).eval a) ((memLp_mulVec (f j) (hε j)).eval b)]
  exact sum_congr rfl fun i _ ↦ by rw [covMat_mulVec (f i) (hε i), hK]

/-- Koja's case 4 (sum of known gains times case 1), recursive form:
`Cov[S (m + 1)] = Cov[S m] + hₘ Wₘ₊₁ hₘᵀ + 2 (hₘ (Wₘ Hₘᵀ - Xₘ))_⊕`, where `2 A_⊕ = A + Aᵀ`,
`Hₖ = ∑_{i < k} hᵢ`, `Wₖ = ∑_{i < k} fᵢ K fᵢᵀ` and `Xₖ = ∑_{i < k} fᵢ K fᵢᵀ Hᵢᵀ`. -/
theorem covMat_case4 [IsFiniteMeasure P] (m : ℕ) (h f : ℕ → Matrix (Fin n) (Fin n) ℝ)
    {ε : ℕ → Ω → Fin n → ℝ} (hε : ∀ k, MemLp (ε k) 2 P)
    (hind : Pairwise fun k j ↦ ε k ⟂ᵢ[P] ε j) {K : Matrix (Fin n) (Fin n) ℝ}
    (hK : ∀ k, covMat (ε k) P = K) {H W X : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ k, H k = ∑ i ∈ range k, h i) (hW : ∀ k, W k = ∑ i ∈ range k, f i * K * (f i)ᵀ)
    (hX : ∀ k, X k = ∑ i ∈ range k, f i * K * (f i)ᵀ * (H i)ᵀ) :
    covMat (fun ω ↦ ∑ k ∈ range (m + 1), h k *ᵥ ∑ i ∈ range (k + 1), f i *ᵥ ε i ω) P
      = covMat (fun ω ↦ ∑ k ∈ range m, h k *ᵥ ∑ i ∈ range (k + 1), f i *ᵥ ε i ω) P
        + h m * W (m + 1) * (h m)ᵀ
        + (h m * (W m * (H m)ᵀ - X m) + (h m * (W m * (H m)ᵀ - X m))ᵀ) := by
  have hQ : ∀ i, (f i * K * (f i)ᵀ)ᵀ = f i * K * (f i)ᵀ := fun i ↦ by
    rw [← hK i, transpose_mul, transpose_mul, covMat_transpose, transpose_transpose,
      Matrix.mul_assoc]
  rw [covMat_case4_closed _ h f hε hind hK hH, covMat_case4_closed _ h f hε hind hK hH,
    sum_sandwich_succ h _ hQ m hH, hW, hW, hX]
  abel

end Case4

/-! ### Case 2 -/

/-- Koja's case 2 (sum of known gains times bias cross product matrix times case 1):
`Cov[∑ₖ hₖ (μ ⨯ ∑_{i ≤ k} fᵢ εᵢ)] = Hₘ Gₘ Hₘᵀ - 2 (Jₘ Hₘᵀ)_⊕ + Kₘ`, where `2 A_⊕ = A + Aᵀ`,
`Bᵢ = Cov[μ] ⊠ (fᵢ Cov[ε] fᵢᵀ)`, `Hₖ = ∑_{i < k} hᵢ`, `Gₖ = ∑_{i < k} Bᵢ`,
`Jₖ = ∑_{i < k} Hᵢ Bᵢ` and `Kₖ = ∑_{i < k} Hᵢ Bᵢ Hᵢᵀ`.
The bias `μ` and the noises `εᵢ` are mutually independent. -/
theorem covMat_case2 [IsProbabilityMeasure P] (m : ℕ) (h f : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
    {μ : Ω → Fin 3 → ℝ} {ε : ℕ → Ω → Fin 3 → ℝ}
    (hind : iIndepFun (fun o : Option ℕ ↦ o.elim μ ε) P) (hμ : MemLp μ 2 P)
    (hε : ∀ k, MemLp (ε k) 2 P) (hμ0 : ∀ i, ∫ ω, μ ω i ∂P = 0)
    (hε0 : ∀ k i, ∫ ω, ε k ω i ∂P = 0) {Kμ Kε : Matrix (Fin 3) (Fin 3) ℝ}
    (hKμ : covMat μ P = Kμ) (hKε : ∀ k, covMat (ε k) P = Kε)
    {H G J K : ℕ → Matrix (Fin 3) (Fin 3) ℝ} (hH : ∀ k, H k = ∑ i ∈ range k, h i)
    (hG : ∀ k, G k = ∑ i ∈ range k, Kμ ⊠ (f i * Kε * (f i)ᵀ))
    (hJ : ∀ k, J k = ∑ i ∈ range k, H i * (Kμ ⊠ (f i * Kε * (f i)ᵀ)))
    (hK : ∀ k, K k = ∑ i ∈ range k, H i * (Kμ ⊠ (f i * Kε * (f i)ᵀ)) * (H i)ᵀ) :
    covMat (fun ω ↦ ∑ k ∈ range m, h k *ᵥ (μ ω ⨯₃ ∑ i ∈ range (k + 1), f i *ᵥ ε i ω)) P
      = H m * G m * (H m)ᵀ - (J m * (H m)ᵀ + (J m * (H m)ᵀ)ᵀ) + K m := by
  classical
  have hm : ∀ o, AEMeasurable ((fun o : Option ℕ ↦ o.elim μ ε) o) P := fun o ↦ by
    cases o
    exacts [hμ.aestronglyMeasurable.aemeasurable, (hε _).aestronglyMeasurable.aemeasurable]
  have hμε : ∀ i, μ ⟂ᵢ[P] ε i := fun i ↦ hind.indepFun (i := none) (j := some i) (by simp)
  have hV : ∀ i, MemLp (fun ω ↦ f i *ᵥ ε i ω) 2 P := fun i ↦ memLp_mulVec (f i) (hε i)
  have hμV : ∀ i, μ ⟂ᵢ[P] fun ω ↦ f i *ᵥ ε i ω := fun i ↦
    (hμε i).comp (φ := id) (ψ := fun v ↦ f i *ᵥ v) measurable_id (by fun_prop)
  have hunc : ∀ i j, i ≠ j → ∀ a b, cov[fun ω ↦ (μ ω ⨯₃ (f i *ᵥ ε i ω)) a,
      fun ω ↦ (μ ω ⨯₃ (f j *ᵥ ε j ω)) b; P] = 0 := by
    intro i j hij a b
    have hi : ε i ⟂ᵢ[P] fun ω ↦ ((μ ω ⨯₃ (f j *ᵥ ε j ω)) b, μ ω) :=
      iIndepFun.indepFun_of_local hind hm (i := some i) (T := {none, some j}) (by simp [hij])
        (Φ := fun G ↦ ((G none ⨯₃ (f j *ᵥ G (some j))) b, G none)) (by fun_prop)
        fun G G' hG ↦ by rw [hG none (by simp), hG (some j) (by simp)]
    have e : (fun ω ↦ (μ ω ⨯₃ (f i *ᵥ ε i ω)) a) = fun ω ↦ -((f i *ᵥ ε i ω) ⨯₃ μ ω) a := by
      ext ω
      rw [← cross_anticomm]
      rfl
    have hiV : (fun ω ↦ f i *ᵥ ε i ω) ⟂ᵢ[P] fun ω ↦ ((μ ω ⨯₃ (f j *ᵥ ε j ω)) b, μ ω) :=
      hi.comp (φ := fun v ↦ f i *ᵥ v) (ψ := id) (by fun_prop) measurable_id
    rw [e, covariance_fun_neg_left, covariance_cross_eq_zero hiV (hV i)
      ((memLp_cross (hμV j) hμ (hV j)).eval b) hμ (integral_mulVec_eq_zero (f i) (hε i) (hε0 i)),
      neg_zero]
  have hB : ∀ i, covMat (fun ω ↦ μ ω ⨯₃ (f i *ᵥ ε i ω)) P = Kμ ⊠ (f i * Kε * (f i)ᵀ) := fun i ↦ by
    rw [covMat_cross_mulVec (hμε i) hμ (hε i) hμ0 (hε0 i), hKμ, hKε]
  have hfun : (fun ω ↦ ∑ k ∈ range m, h k *ᵥ (μ ω ⨯₃ ∑ i ∈ range (k + 1), f i *ᵥ ε i ω))
      = fun ω ↦ ∑ i ∈ range m, (H m - H i) *ᵥ (μ ω ⨯₃ (f i *ᵥ ε i ω)) := by
    ext1 ω
    simp_rw [map_sum (crossProduct (μ _)), sum_mulVec_partialSum, hH]
  rw [hfun, covMat_sum_mulVec_of_uncorrelated _ _
    (fun i ↦ memLp_cross (hμV i) hμ (hV i)) hunc]
  simp_rw [hB]
  rw [sum_sandwich_sub (fun i ↦ by rw [← hB i, covMat_transpose]) m, hG, hJ, hK]

/-! ### Case 3 -/

/-- Koja's case 3 (sum of known gains times noise cross product matrix times case 1), recursive
form: `Cov[S (n + 1)] = hₙ Lₙ₊₁ hₙᵀ + Cov[S n]`, where
`S n = ∑_{m < n} hₘ (ξₘ ⨯ ∑_{k ≤ m} f_k ε_k)` and `Lₖ = ∑_{i < k} Cov[ξ] ⊠ (fᵢ Cov[ε] fᵢᵀ)`.
The noises `ξₘ` and `εₖ` are all mutually independent. -/
theorem covMat_case3 [IsProbabilityMeasure P] (n : ℕ) (h f : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
    {ξ ε : ℕ → Ω → Fin 3 → ℝ} (hind : iIndepFun (Sum.elim ξ ε) P)
    (hξ : ∀ k, MemLp (ξ k) 2 P) (hε : ∀ k, MemLp (ε k) 2 P)
    (hξ0 : ∀ k i, ∫ ω, ξ k ω i ∂P = 0) (hε0 : ∀ k i, ∫ ω, ε k ω i ∂P = 0)
    {Kξ Kε : Matrix (Fin 3) (Fin 3) ℝ} (hKξ : ∀ k, covMat (ξ k) P = Kξ)
    (hKε : ∀ k, covMat (ε k) P = Kε) {L : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    (hL : ∀ k, L k = ∑ i ∈ range k, Kξ ⊠ (f i * Kε * (f i)ᵀ)) :
    covMat (fun ω ↦ ∑ m ∈ range (n + 1), h m *ᵥ (ξ m ω ⨯₃ ∑ k ∈ range (m + 1), f k *ᵥ ε k ω)) P
      = h n * L (n + 1) * (h n)ᵀ
        + covMat (fun ω ↦ ∑ m ∈ range n, h m *ᵥ (ξ m ω ⨯₃ ∑ k ∈ range (m + 1), f k *ᵥ ε k ω))
          P := by
  classical
  let A : ℕ → Ω → Fin 3 → ℝ := fun m ω ↦ ∑ k ∈ range (m + 1), f k *ᵥ ε k ω
  have hm : ∀ o, AEMeasurable (Sum.elim ξ ε o) P := fun o ↦ by
    cases o
    exacts [(hξ _).aestronglyMeasurable.aemeasurable, (hε _).aestronglyMeasurable.aemeasurable]
  have hA : ∀ m, MemLp (A m) 2 P := fun m ↦
    memLp_finsetSum _ fun k _ ↦ memLp_mulVec (f k) (hε k)
  have hA0 : ∀ m p, ∫ ω, A m ω p ∂P = 0 := fun m p ↦ by
    simp only [A, Finset.sum_apply]
    rw [integral_finsetSum _ fun k _ ↦ ((memLp_mulVec (f k) (hε k)).eval p).integrable one_le_two]
    exact sum_eq_zero fun k _ ↦ integral_mulVec_eq_zero (f k) (hε k) (hε0 k) p
  -- `ξ i` is independent of anything built from `ξ j` (`j ≠ i`) and the `ε k`.
  have hloc : ∀ i j N, i ≠ j → ∀ {γ : Type} [MeasurableSpace γ]
      (Φ : (Fin 3 → ℝ) → (ℕ → Fin 3 → ℝ) → γ), Measurable (fun G : ℕ ⊕ ℕ → Fin 3 → ℝ ↦
        Φ (G (.inl j)) fun k ↦ G (.inr k)) →
      (∀ x e e', (∀ k < N, e k = e' k) → Φ x e = Φ x e') →
      ξ i ⟂ᵢ[P] fun ω ↦ Φ (ξ j ω) fun k ↦ ε k ω := by
    intro i j N hij γ _ Φ hΦ hΦloc
    exact iIndepFun.indepFun_of_local hind hm (i := .inl i)
      (T := insert (.inl j) ((range N).image .inr)) (by simp [hij]) hΦ
      fun G G' hG ↦ by
        rw [hG (.inl j) (by simp)]
        exact hΦloc _ _ _ fun k hk ↦ hG (.inr k) (by simp [hk])
  have hsum_loc : ∀ m N, m < N → ∀ e e' : ℕ → Fin 3 → ℝ, (∀ k < N, e k = e' k) →
      ∑ k ∈ range (m + 1), f k *ᵥ e k = ∑ k ∈ range (m + 1), f k *ᵥ e' k :=
    fun m N hmN e e' he ↦ sum_congr rfl fun k hk ↦ by
      rw [he k (by simp at hk; omega)]
  have hξA : ∀ m, ξ m ⟂ᵢ[P] A m := fun m ↦ by
    by_cases hm0 : m = 0
    · subst hm0
      exact hloc 0 1 1 (by simp) (fun _ e ↦ ∑ k ∈ range 1, f k *ᵥ e k) (by fun_prop)
        fun _ e e' he ↦ hsum_loc 0 1 (by simp) e e' he
    · exact hloc m 0 (m + 1) hm0 (fun _ e ↦ ∑ k ∈ range (m + 1), f k *ᵥ e k) (by fun_prop)
        fun _ e e' he ↦ hsum_loc m (m + 1) (by simp) e e' he
  have hunc : ∀ i j, i ≠ j → ∀ a b,
      cov[fun ω ↦ (ξ i ω ⨯₃ A i ω) a, fun ω ↦ (ξ j ω ⨯₃ A j ω) b; P] = 0 := by
    intro i j hij a b
    have hi : ξ i ⟂ᵢ[P] fun ω ↦ ((ξ j ω ⨯₃ A j ω) b, A i ω) :=
      hloc i j (i + j + 1) hij
        (fun x e ↦ ((x ⨯₃ ∑ k ∈ range (j + 1), f k *ᵥ e k) b,
          ∑ k ∈ range (i + 1), f k *ᵥ e k)) (by fun_prop)
        fun x e e' he ↦ by
          rw [hsum_loc j (i + j + 1) (by omega) e e' he,
            hsum_loc i (i + j + 1) (by omega) e e' he]
    exact covariance_cross_eq_zero hi (hξ i) ((memLp_cross (hξA j) (hξ j) (hA j)).eval b) (hA i)
      (hξ0 i) a
  have hX : ∀ m, covMat (fun ω ↦ ξ m ω ⨯₃ A m ω) P = L (m + 1) := fun m ↦ by
    rw [covMat_cross (hξA m) (hξ m) (hA m) (hξ0 m) (hA0 m), hKξ]
    change Kξ ⊠ covMat (fun ω ↦ ∑ k ∈ range (m + 1), f k *ᵥ ε k ω) P = _
    rw [      covMat_sum_mulVec _ f hε
        (fun k j hkj ↦ hind.indepFun (i := .inr k) (j := .inr j) (by simpa using hkj)) hKε, hL]
    exact map_sum (boxTimesₗ Kξ) _ _
  have hc : ∀ n, covMat (fun ω ↦ ∑ m ∈ range n, h m *ᵥ (ξ m ω ⨯₃ A m ω)) P
      = ∑ m ∈ range n, h m * L (m + 1) * (h m)ᵀ := fun n ↦ by
    rw [covMat_sum_mulVec_of_uncorrelated _ h
      (fun m ↦ memLp_cross (hξA m) (hξ m) (hA m)) hunc]
    simp_rw [hX]
  change covMat (fun ω ↦ ∑ m ∈ range (n + 1), h m *ᵥ (ξ m ω ⨯₃ A m ω)) P
    = h n * L (n + 1) * (h n)ᵀ + covMat (fun ω ↦ ∑ m ∈ range n, h m *ᵥ (ξ m ω ⨯₃ A m ω)) P
  rw [hc, hc, sum_range_succ, add_comm]

end Koja
