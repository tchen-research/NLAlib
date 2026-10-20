import NLAlib.Probability.Concentration.Matrix.FiniteHermitianBernstein

/-!
# Actual independent-sum localization at a variance scale

The native finite-dimensional Bernstein theorem gives a useful exponential
bound at an explicit square-root/linear threshold. Source: Tropp (2015),
Theorem 6.1.1, and arXiv:2201.05142v3, the localization step in Section 7.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

private theorem bernsteinTail_le_exp_at_four_sqrt_add
    {v R σ s : ℝ} (hv : 0 ≤ v) (hR : 0 ≤ R) (hσ : 0 ≤ σ)
    (hs : 0 < s) (hscale : 0 < σ+R) (hvariance : v ≤ σ^2) (d : ℕ) :
    bernsteinTail d v R (4*σ*Real.sqrt s+4*R*s) ≤ (d : ℝ)*Real.exp (-s) := by
  let t := 4*σ*Real.sqrt s+4*R*s
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have ht : 0 < t := by
    have hh : 0 < σ ∨ 0 < R := by
      by_cases hpos : 0 < σ
      · exact Or.inl hpos
      · exact Or.inr (by linarith)
    rcases hh with hh | hh <;> dsimp [t] <;> positivity
  have hden : 0 ≤ v+R*t/3 := by positivity
  change bernsteinTail d v R t ≤ _
  by_cases hzero : v+R*t/3 = 0
  · rw [bernsteinTail, if_pos hzero, if_neg ht.ne']
    positivity
  · have hdenpos : 0 < v+R*t/3 := lt_of_le_of_ne hden (Ne.symm hzero)
    have htsq : t^2 = 16*σ^2*s+32*σ*R*s*Real.sqrt s+16*R^2*s^2 := by
      calc
        _ = 16*σ^2*(Real.sqrt s)^2+32*σ*R*s*Real.sqrt s+16*R^2*s^2 := by
          dsimp [t]
          ring
        _ = _ := by rw [Real.sq_sqrt hs.le]
    have hexpand : 2*s*(v+R*t/3) =
        2*s*v+(8/3)*σ*R*s*Real.sqrt s+(8/3)*R^2*s^2 := by dsimp [t]; ring
    have hquad : 2*s*(v+R*t/3) ≤ t^2 := by
      rw [htsq, hexpand]
      have hv' := mul_le_mul_of_nonneg_left hvariance
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs.le)
      have h1 : 0 ≤ σ^2*s := mul_nonneg (sq_nonneg _) hs.le
      have h2 : 0 ≤ σ*R*s*Real.sqrt s := by positivity
      have h3 : 0 ≤ R^2*s^2 := by positivity
      nlinarith only [hv', h1, h2, h3]
    rw [bernsteinTail, if_neg hzero]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hdenpos).mpr
    nlinarith only [hquad]

open scoped Matrix.Norms.L2Operator in
/-- A bounded independent centered Hermitian sum has norm at most
`4*σ*sqrt(s)+4*R*s` except on probability `2*d*exp(-s)`, whenever the
displayed scale is positive. All moments and the product law are actual.
The zero-scale case is treated separately by almost-everywhere vanishing.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_specNorm_sum_pi_gt_four_sqrt_add_le
    {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Nonempty n]
    [MeasurableSpace Ω]
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R σ s : ℝ} (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hs : 0 < s) (hscale : 0 < σ+R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (hvariance : specNorm (∑ i, ∫ ω, Z i ω^2 ∂ν i) ≤ σ^2) :
    (Measure.pi ν).real {x : ι → Ω |
      4*σ*Real.sqrt s+4*R*s < specNorm (∑ i, Z i (x i))} ≤
        (2*Fintype.card n : ℝ)*Real.exp (-s) := by
  classical
  let Y (i : ι) (x : ι → Ω) := Z i (x i)
  have hYm : ∀ i, Measurable (Y i) := fun i => (hZm i).comp (measurable_pi_apply i)
  have hYH : ∀ i, ∀ᵐ x ∂Measure.pi ν, (Y i x).IsHermitian := fun i =>
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZH i)
  have hYB : ∀ i, ∀ᵐ x ∂Measure.pi ν, specNorm (Y i x) ≤ R := fun i =>
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZ i)
  have hYmean : ∀ i, ∫ x, Y i x ∂Measure.pi ν = 0 := by
    intro i
    rw [show (∫ x, Y i x ∂Measure.pi ν) = ∫ ω, Z i ω ∂ν i from
      integral_comp_eval (μ := ν) (i := i) (hZm i).aestronglyMeasurable, hmean]
  have hYsq : (∑ i, ∫ x, Y i x^2 ∂Measure.pi ν) = ∑ i, ∫ ω, Z i ω^2 ∂ν i := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Y, pow_two] using integral_comp_eval (μ := ν) (i := i)
      ((hZm i).matrix_mul (hZm i)).aestronglyMeasurable
  have ht : 0 ≤ 4*σ*Real.sqrt s+4*R*s := by positivity
  have hraw := (integral_and_measureReal_specNorm_sum_le_bernstein_hermitian
    (Measure.pi ν) Y hR hYm (iIndepFun_pi fun i => (hZm i).aemeasurable)
      hYH hYB hYmean).2 _ ht
  rw [hYsq] at hraw
  have hsub : {x : ι → Ω | 4*σ*Real.sqrt s+4*R*s < specNorm (∑ i, Z i (x i))} ⊆
      {x : ι → Ω | 4*σ*Real.sqrt s+4*R*s ≤ specNorm (∑ i, Y i x)} := by
    intro x hx
    change 4*σ*Real.sqrt s+4*R*s < specNorm (∑ i, Z i (x i)) at hx
    change 4*σ*Real.sqrt s+4*R*s ≤ specNorm (∑ i, Z i (x i))
    exact hx.le
  apply (measureReal_mono (μ := Measure.pi ν) hsub).trans (hraw.trans ?_)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    bernsteinTail_le_exp_at_four_sqrt_add (specNorm_nonneg _) hR hσ hs hscale hvariance
      (2*Fintype.card n)

end NLAlib
