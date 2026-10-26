/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.Kaczmarz.TailMoment
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tail-averaged randomized Kaczmarz under its actual row law

The first path supplies the burn-in updates; the independent second path supplies the
averaging updates. Both have the native squared-row-norm product law. The estimator
averages exactly `x_b, ..., x_(b+N-1)`, so the last sampled row is unused.
Source: Epperly–Goldshlager–Webber, arXiv:2411.19877v3, Theorems 2–3.
Atlas: `tail-averaged-kaczmarz`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib.Kaczmarz
variable {m n : Type*} [Fintype m] [Fintype n]

/-- Tail average after `burn` updates, averaging `N` consecutive actual iterates. The two
paths are the burn-in and subsequent row choices. The total definition returns zero for
`N=0`; all accuracy bounds require `0<N`. -/
def tailAverage (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) (burn N : ℕ)
    (ω : (Fin burn → m) × (Fin N → m)) : n → ℝ :=
  (N : ℝ)⁻¹ • runSum A b N ω.2 (run A b burn ω.1 x)

omit [Fintype m] in
private theorem tailAverage_sub_eq (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ)
    (burn N : ℕ) (hN : 0 < N) (ω : (Fin burn → m) × (Fin N → m)) :
    tailAverage A b x burn N ω - xs =
      (N : ℝ)⁻¹ • runSumError A b xs N ω.2 (run A b burn ω.1 x) := by
  rw [tailAverage, runSumError, smul_sub, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)), one_smul]

private theorem run_sub_mem_range [DecidableEq m]
    (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ)
    (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) (ω : Fin k → m) :
    run A b k ω x - xs ∈ LinearMap.range Aᵀ.mulVecLin := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    exact ih _ (step_sub_mem_range_of_sub_mem_range A b xs x hx (ω 0)) (Fin.tail ω)

private theorem sum_two_paths_dotProduct_runSumError_le [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs : n → ℝ)
    (hxs : IsLeastSquaresSolution A b xs) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (burn N : ℕ) :
    let q := 1 - σ ^ 2 / frobSq A
    let V := ((b - A *ᵥ xs) ⬝ᵥ (b - A *ᵥ xs)) / σ ^ 2
    (∑ ω₁ : Fin burn → m, (∏ j, prob A (ω₁ j)) *
      (∑ ω₂ : Fin N → m, (∏ j, prob A (ω₂ j)) *
        (runSumError A b xs N ω₂ (run A b burn ω₁ x) ⬝ᵥ
          runSumError A b xs N ω₂ (run A b burn ω₁ x)))) ≤
      tailInitialWeight q N * q ^ burn * ((x - xs) ⬝ᵥ (x - xs)) +
        ((1 + q) / (1 - q)) * N * V := by
  dsimp only
  let q := 1 - σ ^ 2 / frobSq A
  let V := ((b - A *ᵥ xs) ⬝ᵥ (b - A *ᵥ xs)) / σ ^ 2
  let C := (1 + q) / (1 - q)
  have hq0 : 0 ≤ q := rate_nonneg_of_lower_bound_on_range A σ hσ
  calc
    _ ≤ ∑ ω₁ : Fin burn → m, (∏ j, prob A (ω₁ j)) *
        (tailInitialWeight q N * ((run A b burn ω₁ x - xs) ⬝ᵥ
          (run A b burn ω₁ x - xs)) + (C * N - tailInitialWeight q N) * V) :=
      Finset.sum_le_sum fun ω₁ _ => mul_le_mul_of_nonneg_left
        (by
          have hσnorm : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
              σ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 ≤ ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2 := by
            simpa only [norm_toLp_sq_eq_dotProduct_self] using hσ
          simpa only [norm_toLp_sq_eq_dotProduct_self] using
            sum_paths_norm_runSumError_sq_le A hA b xs hxs hσ0 hσnorm _
              (run_sub_mem_range A b xs x hx burn ω₁) N)
        (Finset.prod_nonneg fun j _ => prob_nonneg A (ω₁ j))
    _ = tailInitialWeight q N * expErr A b xs x burn +
        (C * N - tailInitialWeight q N) * V := by
      rw [expErr_eq_sum_paths]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_prod_prob A hA, one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ tailInitialWeight q N * (q ^ burn * ((x - xs) ⬝ᵥ (x - xs)) + V) +
        (C * N - tailInitialWeight q N) * V :=
      add_le_add (mul_le_mul_of_nonneg_left
        (expErr_le_add_div_sq_of_sub_mem_range A b xs hσ0 hσ x hx burn)
        (tailInitialWeight_nonneg hq0 N)) le_rfl
    _ = _ := by ring

private theorem integral_dotProduct_tailAverage_sub_eq
    [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs x : n → ℝ)
    (burn N : ℕ) (hN : 0 < N) :
    (∫ ω, (tailAverage A b x burn N ω - xs) ⬝ᵥ (tailAverage A b x burn N ω - xs)
      ∂((kaczmarzRowPathPMF A hA burn).toMeasure.prod
        (kaczmarzRowPathPMF A hA N).toMeasure)) =
      (N : ℝ)⁻¹ ^ 2 *
      (∑ ω₁ : Fin burn → m, (∏ j, prob A (ω₁ j)) *
        (∑ ω₂ : Fin N → m, (∏ j, prob A (ω₂ j)) *
          (runSumError A b xs N ω₂ (run A b burn ω₁ x) ⬝ᵥ
            runSumError A b xs N ω₂ (run A b burn ω₁ x)))) := by
  classical
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [PMF.integral_eq_sum, tailAverage_sub_eq A b xs x burn N hN]
  have hw (k : ℕ) (ω : Fin k → m) : (kaczmarzRowPathPMF A hA k ω).toReal =
      ∏ j, prob A (ω j) := by
    simp only [kaczmarzRowPathPMF, PMF.ofFintype_apply]
    exact ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => prob_nonneg A (ω j))
  simp_rw [hw, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω₁ _
  apply Finset.sum_congr rfl
  intro ω₂ _
  ring

/-- **Actual-law tail-average moment with the finite transient coefficient.** The integral
is under independent native row-path laws for burn-in and averaging.
atlas: tail-averaged-kaczmarz (partial) -/
theorem integral_norm_tailAverage_sub_sq_le [DecidableEq m] [DecidableEq n]
    [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs : n → ℝ)
    (hxs : IsLeastSquaresSolution A b xs) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 ≤ ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2)
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin)
    (burn N : ℕ) (hN : 0 < N) :
    let q := 1 - σ ^ 2 / frobSq A
    let V := ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / σ ^ 2
    (∫ ω, ‖WithLp.toLp 2 (tailAverage A b x burn N ω - xs)‖ ^ 2
      ∂((kaczmarzRowPathPMF A hA burn).toMeasure.prod
        (kaczmarzRowPathPMF A hA N).toMeasure)) ≤
      (tailInitialWeight q N / (N : ℝ) ^ 2) * q ^ burn * ‖WithLp.toLp 2 (x - xs)‖ ^ 2 +
        ((1 + q) / (1 - q)) * V / N := by
  simp only [norm_toLp_sq_eq_dotProduct_self] at hσ ⊢
  rw [integral_dotProduct_tailAverage_sub_eq A hA b xs x burn N hN]
  apply (mul_le_mul_of_nonneg_left
    (sum_two_paths_dotProduct_runSumError_le A hA b xs hxs hσ0 hσ x hx burn N)
    (sq_nonneg (N : ℝ)⁻¹)).trans_eq
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]

end NLAlib.Kaczmarz
