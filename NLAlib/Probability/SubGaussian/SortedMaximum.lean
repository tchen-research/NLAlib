import NLAlib.Probability.SubGaussian.ExpSquare
import NLAlib.ForMathlib.MeasureTheory.IntegralSqrt
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Dimension-free maxima from a sorted variance envelope

Square-exponential moments and summable rank weights bound a finite
sub-Gaussian maximum by `max_i sqrt(c_i log(i+2))`. Independence is not
needed. This is the scalar maximal estimate used in van Handel,
arXiv:1502.05003v4, Theorem 4.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace NLAlib

private theorem sum_fin_inv_add_two_sq_le (n : ℕ) :
    (∑ i : Fin n, ((((i : ℕ) : ℝ) + 2) ^ 2)⁻¹) ≤ 1 := by
  have hstrong (m : ℕ) : (∑ i : Fin m, ((((i : ℕ) : ℝ) + 2) ^ 2)⁻¹) ≤
      1 - ((m : ℝ) + 1)⁻¹ := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
      have hstep : (((m : ℝ) + 2) ^ 2)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ - ((m : ℝ) + 2)⁻¹ := by
        have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
        field_simp
        nlinarith
      linarith
  exact (hstrong n).trans (sub_le_self _ (inv_nonneg.mpr (by positivity)))

private theorem sq_le_rank_weighted_exponential (x D l : ℝ) (hD : 0 < D) (hl : 1 / 2 ≤ l) :
    x ^ 2 ≤ 32 * D ^ 2 + 32 * D ^ 2 * Real.exp (l * (x ^ 2 / (16 * D ^ 2) - 2)) := by
  let u := x ^ 2 / (16 * D ^ 2) - 2
  have hprod : x ^ 2 = 16 * D ^ 2 * (u + 2) := by dsimp [u]; field_simp; ring
  have hexp : u ≤ 2 * Real.exp (l * u) := by
    by_cases hu : u ≤ 0
    · exact hu.trans (by positivity)
    · have hu0 : 0 ≤ u := (lt_of_not_ge hu).le
      have h1 := Real.add_one_le_exp (l * u)
      nlinarith [mul_le_mul_of_nonneg_right hl hu0]
  change x ^ 2 ≤ 32 * D ^ 2 + 32 * D ^ 2 * Real.exp (l * u)
  nlinarith [sq_nonneg D]

/-- A finite family of actual sub-Gaussian variables has a dimension-free
expected maximum whenever its variance proxies obey a logarithmic rank
envelope. No independence is required, and zero proxies are allowed. -/
theorem integral_norm_pi_le_sixteen_of_hasSubgaussianMGF_log_envelope
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (c : Fin n → ℝ≥0)
    (hX : ∀ i, HasSubgaussianMGF (X i) (c i) μ) (D : ℝ) (hD : 0 < D)
    (henv : ∀ i, (c i : ℝ) * Real.log (((i : ℕ) : ℝ) + 2) ≤ D ^ 2) :
    (∫ ω, ‖fun i => X i ω‖ ∂μ) ≤ 16 * D := by
  let l : Fin n → ℝ := fun i => Real.log (((i : ℕ) : ℝ) + 2)
  let θ : Fin n → ℝ := fun i => l i / (16 * D ^ 2)
  let C : Fin n → ℝ := fun i => D ^ 2 / l i
  let F : Fin n → Ω → ℝ := fun i ω =>
    Real.exp (θ i * X i ω ^ 2) / ((((i : ℕ) : ℝ) + 2) ^ 2)
  have hl (i : Fin n) : 1 / 2 ≤ l i := by
    have h2 : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact h2.trans (Real.log_le_log (by norm_num) (by
      have hi : 0 ≤ (((i : ℕ) : ℝ)) := Nat.cast_nonneg _
      linarith))
  have hl0 (i : Fin n) : 0 < l i := lt_of_lt_of_le (by norm_num) (hl i)
  have hθ (i : Fin n) : 0 ≤ θ i := div_nonneg (hl0 i).le (by positivity)
  have hC (i : Fin n) : 0 < C i := div_pos (sq_pos_of_pos hD) (hl0 i)
  have hc (i : Fin n) : (c i : ℝ) ≤ C i := (le_div_iff₀ (hl0 i)).mpr (henv i)
  have hθC (i : Fin n) : θ i * C i = 1 / 16 := by
    dsimp [θ, C]
    field_simp [(hl0 i).ne', hD.ne']
  have hsmall (i : Fin n) : θ i * C i * Real.exp 1 < 1 := by
    rw [hθC]
    linarith [Real.exp_one_lt_three]
  have hExp (i : Fin n) : Integrable (fun ω => Real.exp (θ i * X i ω ^ 2)) μ :=
    integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le (hX i) (hθ i) (hC i) (hc i) (hsmall i)
  have hExpBound (i : Fin n) : (∫ ω, Real.exp (θ i * X i ω ^ 2) ∂μ) ≤ 4 := by
    have h := integral_exp_mul_sq_le_of_hasSubgaussianMGF
      (hX i) (hθ i) (hC i) (hc i) (hsmall i)
    rw [hθC] at h
    apply h.trans
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith [Real.exp_one_lt_three] :
      0 < 1 - (1 / 16 : ℝ) * Real.exp 1)]
    linarith [Real.exp_one_lt_three]
  have hFi (i : Fin n) : Integrable (F i) μ := (hExp i).div_const _
  have hFb (i : Fin n) : (∫ ω, F i ω ∂μ) ≤ 4 / ((((i : ℕ) : ℝ) + 2) ^ 2) := by
    rw [show (∫ ω, F i ω ∂μ) =
      (∫ ω, Real.exp (θ i * X i ω ^ 2) ∂μ) / ((((i : ℕ) : ℝ) + 2) ^ 2) from integral_div ..]
    exact div_le_div_of_nonneg_right (hExpBound i) (sq_nonneg _)
  have hW2 : MemLp (fun ω => fun i => X i ω) 2 μ := by
    apply memLp_pi_iff.mpr
    intro i
    apply (memLp_two_iff_integrable_sq (hX i).aemeasurable.aestronglyMeasurable).mpr
    exact integrable_pow_of_integrable_exp_mul one_ne_zero
      ((hX i).integrable_exp_mul 1) ((hX i).integrable_exp_mul (-1)) 2
  have hpoint (ω : Ω) : ‖fun i => X i ω‖ ^ 2 ≤
      32 * D ^ 2 + 32 * D ^ 2 * ∑ i, F i ω := by
    have hcoord (i : Fin n) : X i ω ^ 2 ≤
        32 * D ^ 2 + 32 * D ^ 2 * ∑ j, F j ω := by
      have h := sq_le_rank_weighted_exponential (X i ω) D (l i) hD (hl i)
      have he : Real.exp (l i * (X i ω ^ 2 / (16 * D ^ 2) - 2)) = F i ω := by
        have hearg : l i * (X i ω ^ 2 / (16 * D ^ 2) - 2) = θ i * X i ω ^ 2 - 2 * l i := by
          dsimp [θ]; ring
        rw [hearg, Real.exp_sub]
        dsimp [F, l]
        rw [two_mul, Real.exp_add, Real.exp_log (by positivity), sq]
        ring
      rw [he] at h
      exact h.trans (by
        gcongr
        exact Finset.single_le_sum (f := fun j => F j ω)
          (fun j _ => by dsimp [F]; positivity) (Finset.mem_univ i))
    have hS : 0 ≤ 32 * D ^ 2 + 32 * D ^ 2 * ∑ i, F i ω := by
      dsimp [F]; positivity
    have hnorm : ‖fun i => X i ω‖ ≤ Real.sqrt (32 * D ^ 2 + 32 * D ^ 2 * ∑ i, F i ω) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro i
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hcoord i)
    nlinarith [Real.sq_sqrt hS, norm_nonneg (fun i => X i ω)]
  have hsum : (∑ i, ∫ ω, F i ω ∂μ) ≤ 4 := by
    calc _ ≤ ∑ i : Fin n, 4 / ((((i : ℕ) : ℝ) + 2) ^ 2) := Finset.sum_le_sum fun i _ => hFb i
      _ = 4 * ∑ i : Fin n, ((((i : ℕ) : ℝ) + 2) ^ 2)⁻¹ := by simp [div_eq_mul_inv, Finset.mul_sum]
      _ ≤ 4 := by nlinarith [sum_fin_inv_add_two_sq_le n]
  have hsquare := integral_mono hW2.norm.integrable_sq
    ((integrable_const _).add ((integrable_finsetSum _ (fun i _ => hFi i)).const_mul _)) hpoint
  simp only [Pi.add_apply] at hsquare
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ (fun i _ => hFi i)).const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum _ (fun i _ => hFi i)] at hsquare
  apply integral_le_of_integral_sq_le μ _ (hW2.norm.integrable (by norm_num))
    hW2.norm.integrable_sq (16 * D) (by positivity)
  nlinarith [sq_nonneg D]

end NLAlib
