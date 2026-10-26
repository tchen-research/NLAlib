/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.Kaczmarz.TailSum
import NLAlib.Solvers.Kaczmarz.TailWeights

/-!
# Second moment of sums of Kaczmarz errors

A first-step induction retains the finite initial-error coefficient and the geometric
noise constant. This is an algebraic reorganization of the two-time correlation proof;
the same random trajectory supplies every summand.
Source: Epperly–Goldshlager–Webber, arXiv:2411.19877v3, Theorems 2–3.
Atlas: `tail-averaged-kaczmarz` (moment kernel).
-/

noncomputable section
open scoped Matrix
namespace NLAlib.Kaczmarz
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Finite tail-sum moment.** The exact initial-error coefficient is retained, while
the noise coefficient is at most `N(1+q)/(1-q) - tailInitialWeight q N`.
Only a lower singular bound on the row space is assumed. -/
theorem sum_paths_norm_runSumError_sq_le
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs : n → ℝ)
    (hxs : IsLeastSquaresSolution A b xs) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 ≤ ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2)
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (N : ℕ) :
    let q := 1 - σ ^ 2 / frobSq A
    let V := ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / σ ^ 2
    (∑ ω : Fin N → m, (∏ j, prob A (ω j)) *
      ‖WithLp.toLp 2 (runSumError A b xs N ω x)‖ ^ 2) ≤
      tailInitialWeight q N * ‖WithLp.toLp 2 (x - xs)‖ ^ 2 +
        (((1 + q) / (1 - q)) * N - tailInitialWeight q N) * V := by
  have hσnorm := hσ
  simp only [norm_toLp_sq_eq_dotProduct_self] at hσ ⊢
  let q := 1 - σ ^ 2 / frobSq A
  let V := ((b - A *ᵥ xs) ⬝ᵥ (b - A *ᵥ xs)) / σ ^ 2
  let C := (1 + q) / (1 - q)
  change _ ≤ tailInitialWeight q N * _ + (C * N - tailInitialWeight q N) * V
  have hF : 0 < frobSq A := lt_of_le_of_ne (frobSq_nonneg A)
    (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  have hq0 : 0 ≤ q := rate_nonneg_of_lower_bound_on_range A σ hσ
  have hq1 : q < 1 := by
    dsimp [q]
    have hp : 0 < σ ^ 2 / frobSq A := div_pos (sq_pos_of_pos hσ0) hF
    linarith
  have hV : 0 ≤ V := div_nonneg (dotProduct_self_nonneg _) (sq_nonneg σ)
  have hnoise : (1 - q) * V = ((b - A *ᵥ xs) ⬝ᵥ (b - A *ᵥ xs)) / frobSq A := by
    dsimp [q, V]
    field_simp [ne_of_gt hσ0, ne_of_gt hF]
    ring
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
    let E := (x - xs) ⬝ᵥ (x - xs)
    let G := ∑ t ∈ Finset.range N, q ^ (t + 1)
    have hmean : (x - xs) ⬝ᵥ (∑ ω : Fin (N + 1) → m,
        (∏ j, prob A (ω j)) • runSumError A b xs (N + 1) ω x) ≤ (1 + G) * E := by
      rw [sum_paths_smul_runSumError_eq_sum_pow_mulVec A hA b xs hxs x (N + 1),
        dotProduct_sum]
      calc
        _ ≤ ∑ t ∈ Finset.range (N + 1), q ^ t * E := by
          apply Finset.sum_le_sum
          intro t _
          exact (le_abs_self _).trans
            (by simpa only [norm_toLp_sq_eq_dotProduct_self] using
              abs_dotProduct_pow_meanError_mulVec_le_of_mem_range A hA σ hσnorm _ hx t)
        _ = (1 + G) * E := by
          rw [← Finset.sum_mul, Finset.sum_range_succ']
          simp only [pow_zero]
          dsimp [G]
          ring
    have hstep : (∑ i, prob A i * ((step A b x i - xs) ⬝ᵥ (step A b x i - xs))) ≤
        q * E + (1 - q) * V := by
      rw [hnoise]
      exact expected_sqErr_step_le_add_of_sub_mem_range A b xs x σ hσ hx
    have hfuture :
        (∑ i, prob A i * (∑ ω : Fin N → m, (∏ j, prob A (ω j)) *
          (runSumError A b xs N ω (step A b x i) ⬝ᵥ
            runSumError A b xs N ω (step A b x i)))) ≤
        tailInitialWeight q N * (q * E + (1 - q) * V) +
          (C * N - tailInitialWeight q N) * V := by
      calc
        _ ≤ ∑ i, prob A i *
            (tailInitialWeight q N * ((step A b x i - xs) ⬝ᵥ (step A b x i - xs)) +
              (C * N - tailInitialWeight q N) * V) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (ih _ (step_sub_mem_range_of_sub_mem_range A b xs x hx i)) (prob_nonneg A i)
        _ = tailInitialWeight q N *
            (∑ i, prob A i * ((step A b x i - xs) ⬝ᵥ (step A b x i - xs))) +
              (C * N - tailInitialWeight q N) * V := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_prob A hA,
            one_mul, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left hstep (tailInitialWeight_nonneg hq0 N)) le_rfl
    have hrec := sum_paths_norm_runSumError_sq_succ A hA b xs x N
    simp only [norm_toLp_sq_eq_dotProduct_self] at hrec
    rw [hrec]
    have hc : 1 + 2 * G ≤ C := one_add_two_mul_sum_pow_succ_le hq0 hq1 N
    have ht : tailInitialWeight q (N + 1) = 1 + 2 * G + q * tailInitialWeight q N :=
      tailInitialWeight_succ q N
    rw [ht]
    simp only [Nat.cast_add, Nat.cast_one]
    have hcv := mul_le_mul_of_nonneg_right hc hV
    change -E + 2 * _ + _ ≤ _
    nlinarith only [hmean, hfuture, hcv]

end NLAlib.Kaczmarz
