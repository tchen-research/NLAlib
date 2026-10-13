import NLAlib.Matrix.Norms.Net
import Mathlib.Probability.Moments.SubGaussian

/-!
# The spectral norm of a matrix with sub-Gaussian bilinear marginals

`measure_lt_specNorm_le_of_hasSubgaussianMGF`: tail of `‖A‖₂` for a random matrix with
sub-Gaussian bilinear marginals (Vershynin 2018, Thm 4.4.5, explicit constants), by a union bound
over the 1/4-nets of `Matrix/Norms/Net` (where the deterministic ε-net lemmas live).

Atlas `subgaussian-spec-norm` (new). Audit G1 B2.
-/

open MeasureTheory Metric ProbabilityTheory
open scoped NNReal
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace NLAlib

/-- **Spectral norm of a matrix with sub-Gaussian bilinear marginals.** If
`yᵀ A x` is sub-Gaussian with proxy `c` for all unit `x ∈ ℝⁿ`, `y ∈ ℝᵐ` (no independence is
assumed), then for `t ≥ 0`,
`P(‖A‖₂ > 2(√(2 log 9 · (m + n) c) + √c t)) ≤ e^{-t²/2}`.
The inequality is strict: with `≤` the statement fails for `c = 0`.
Vershynin 2018, Thm 4.4.5 (with explicit constants: 1/4-nets of size `9ⁿ`, `9ᵐ`, the bilinear
net lemma and a union bound); audit G1 B2. Atlas `subgaussian-spec-norm` (new). No
measurability hypothesis is needed (outer measure).
atlas: subgaussian-spec-norm -/
theorem measure_lt_specNorm_le_of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Ω → Matrix m n ℝ) (c : ℝ≥0)
    (hA : ∀ (x : n → ℝ) (y : m → ℝ), x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 →
      HasSubgaussianMGF (fun ω => y ⬝ᵥ (A ω *ᵥ x)) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | 2 * (√(2 * Real.log 9 * (Fintype.card m + Fintype.card n) * c) + √c * t) <
        specNorm (A ω)} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  classical
  set a := √(2 * Real.log 9 * (Fintype.card m + Fintype.card n) * c) with ha
  set u := a + √c * t with hu
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_finset_sphere_net n (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨N', hN'1, hN'2, hN'3⟩ := exists_finset_sphere_net m (show (0 : ℝ) < 1 / 4 by norm_num)
  have h9 : (1 + 2 / (1 / 4 : ℝ)) = 9 := by norm_num
  rw [h9] at hN2 hN'2
  -- the event is covered by the union of the bilinear events over the nets
  have hsub : {ω | 2 * u < specNorm (A ω)} ⊆
      ⋃ x ∈ N, ⋃ y ∈ N', {ω | u < y ⬝ᵥ (A ω *ᵥ x)} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
    have := specNorm_le_div_of_net_bilinear (A ω) N N' (by norm_num) (by norm_num) hu0 hN'1
      hN3 hN'3 fun x hx y hy => hnot x hx y hy
    rw [Set.mem_ofPred_eq] at hω
    have h2 : u / (1 - 2 * (1 / 4 : ℝ)) = 2 * u := by ring
    linarith
  have hunion : μ {ω | 2 * u < specNorm (A ω)} ≤
      ∑ x ∈ N, ∑ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} :=
    calc μ {ω | 2 * u < specNorm (A ω)}
        ≤ μ (⋃ x ∈ N, ⋃ y ∈ N', {ω | u < y ⬝ᵥ (A ω *ᵥ x)}) := measure_mono hsub
      _ ≤ ∑ x ∈ N, μ (⋃ y ∈ N', {ω | u < y ⬝ᵥ (A ω *ᵥ x)}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ N, ∑ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} :=
          Finset.sum_le_sum fun x _ => measure_biUnion_finset_le _ _
  refine hunion.trans ?_
  rcases eq_or_ne c 0 with hc | hc
  · -- `c = 0`: every bilinear marginal vanishes a.s.
    subst hc
    have hzero : ∀ x ∈ N, ∀ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} = 0 := by
      intro x hx y hy
      have h0 := (hA x y (hN1 x hx) (hN'1 y hy)).ae_eq_zero_of_hasSubgaussianMGF_zero
      have hu' : u = 0 := by simp [hu, ha]
      apply measure_mono_null (t := {ω | (fun ω => y ⬝ᵥ (A ω *ᵥ x)) ω ≠ (0 : Ω → ℝ) ω})
      · intro ω hω h
        simp only [Set.mem_ofPred_eq, Pi.zero_apply] at hω h
        linarith
      · exact ae_iff.1 h0
    rw [Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => hzero x hx y hy]
    exact zero_le
  have hc0 : (0 : ℝ) < c := lt_of_le_of_ne c.2 (by exact_mod_cast hc.symm)
  have hterm : ∀ x ∈ N, ∀ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} ≤
      ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * c))) := by
    intro x hx y hy
    have hsg := hA x y (hN1 x hx) (hN'1 y hy)
    calc μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)} ≤ μ {ω | u ≤ y ⬝ᵥ (A ω *ᵥ x)} :=
          measure_mono fun ω hω => by
            simp only [Set.mem_ofPred_eq] at hω ⊢; exact hω.le
      _ = ENNReal.ofReal (μ.real {ω | u ≤ y ⬝ᵥ (A ω *ᵥ x)}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hsg.measure_ge_le hu0)
  -- the union bound
  set k : ℕ := Fintype.card m + Fintype.card n with hk
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have ha2 : a ^ 2 = 2 * Real.log 9 * k * c := by
    rw [ha, Real.sq_sqrt (by positivity), hk]; push_cast; ring
  have hsc : √(c : ℝ) ^ 2 = c := Real.sq_sqrt c.2
  have hu2 : 2 * Real.log 9 * k * c + c * t ^ 2 ≤ u ^ 2 := by
    have : u ^ 2 = a ^ 2 + 2 * a * (√c * t) + √(c : ℝ) ^ 2 * t ^ 2 := by rw [hu]; ring
    rw [this, ha2, hsc]
    nlinarith [mul_nonneg (mul_nonneg ha0 (Real.sqrt_nonneg (c : ℝ))) ht]
  have hexp : Real.exp (-u ^ 2 / (2 * c)) ≤
      Real.exp (-(k * Real.log 9)) * Real.exp (-t ^ 2 / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcard : (N.card : ℝ) * N'.card ≤ Real.exp (k * Real.log 9) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num), hk, pow_add, mul_comm]
    exact mul_le_mul hN'2 hN2 (by positivity) (by positivity)
  have hrhs : (N.card : ℝ) * N'.card * Real.exp (-u ^ 2 / (2 * c)) ≤ Real.exp (-t ^ 2 / 2) := by
    calc (N.card : ℝ) * N'.card * Real.exp (-u ^ 2 / (2 * c))
        ≤ Real.exp (k * Real.log 9) * (Real.exp (-(k * Real.log 9)) * Real.exp (-t ^ 2 / 2)) :=
          mul_le_mul hcard hexp (by positivity) (by positivity)
      _ = Real.exp (-t ^ 2 / 2) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  calc ∑ x ∈ N, ∑ y ∈ N', μ {ω | u < y ⬝ᵥ (A ω *ᵥ x)}
      ≤ ∑ x ∈ N, ∑ y ∈ N', ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * c))) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hterm x hx y hy
    _ = ENNReal.ofReal ((N.card : ℝ) * N'.card * Real.exp (-u ^ 2 / (2 * c))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hrhs

end NLAlib
