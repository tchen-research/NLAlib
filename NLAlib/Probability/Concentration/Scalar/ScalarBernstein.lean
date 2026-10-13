import NLAlib.Probability.SubGaussian.OrliczMGF

/-!
# Scalar Bernstein inequality from Orlicz bounds

Independent centered coordinates satisfying `E exp(|Xᵢ|/Kᵢ) ≤ 2` obey
`P(|Σ Xᵢ| ≥ t) ≤ 2 exp(-min(t²/Σ Kᵢ², t/B)/64)`, where `B>0` dominates the scales. The
Chernoff step is the general local-CGF tail bound `measureReal_ge_le_exp_of_cgf_le` (and its
two-sided form), shared with the Hanson–Wright proof.
All moments and local exponential integrability are derived from the nonnegative Orlicz
expectations. The sum may be empty. The constant `1/64` is conservative.

Vershynin 2018, Theorem 2.8.4; atlas `bernstein-scalar`.
The independent-MGF factorization is Mathlib's theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace NLAlib

/-- Independent `ψ₁` bounds give exponential integrability of the sum for tilts of radius
`1/(2B)`, where `B` dominates the scales. Vershynin 2018, proof of Theorem 2.8.4. -/
theorem integrable_exp_mul_sum_of_lintegral_exp_abs_le_two
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (K : ι → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (hK : ∀ i, 0 < K i)
    (hpsi : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|X i ω| / K i)) ∂μ ≤ 2)
    (B : ℝ) (hKB : ∀ i, K i ≤ B) (s : ℝ) (hs : |s| ≤ 1 / (2 * B)) :
    Integrable (fun ω => Real.exp (s * ∑ i, X i ω)) μ := by
  have hdomain : ∀ i, |s| ≤ 1 / (2 * K i) := fun i => hs.trans
    (one_div_le_one_div_of_le (mul_pos (by norm_num) (hK i)) (by nlinarith [hKB i]))
  simpa only [Finset.sum_apply] using hind.integrable_exp_mul_sum
    (t := s) hX (s := Finset.univ) (fun i _ => integrable_exp_mul_of_lintegral_exp_abs_le_two
      (hX i).aemeasurable (K i) (hK i) (hpsi i) (hdomain i))

/-- Independent centered `ψ₁` bounds give the local MGF bound for the sum, with quadratic
proxy `16ΣKᵢ²` and radius `1/(2B)` (integrability:
`integrable_exp_mul_sum_of_lintegral_exp_abs_le_two`).
Vershynin 2018, proof of Theorem 2.8.4; atlas `bernstein-scalar` (MGF assembly). -/
theorem mgf_sum_le_of_lintegral_exp_abs_le_two
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (K : ι → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hK : ∀ i, 0 < K i) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hpsi : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|X i ω| / K i)) ∂μ ≤ 2)
    (B : ℝ) (hKB : ∀ i, K i ≤ B) (s : ℝ) (hs : |s| ≤ 1 / (2 * B)) :
    mgf (fun ω => ∑ i, X i ω) μ s ≤ Real.exp (16 * (∑ i, K i ^ 2) * s ^ 2) := by
  classical
  have hdomain : ∀ i, |s| ≤ 1 / (2 * K i) := fun i => hs.trans
    (one_div_le_one_div_of_le (mul_pos (by norm_num) (hK i)) (by nlinarith [hKB i]))
  have heq : mgf (fun ω => ∑ i, X i ω) μ s = ∏ i, mgf (X i) μ s := by
    have hfun : (∑ i, X i) = fun ω => ∑ i, X i ω := by
      funext ω
      simp only [Finset.sum_apply]
    rw [← hfun]
    exact hind.mgf_sum (t := s) hX Finset.univ
  rw [heq]
  calc
    ∏ i, mgf (X i) μ s ≤ ∏ i, Real.exp (16 * K i ^ 2 * s ^ 2) :=
      Finset.prod_le_prod (fun _ _ => mgf_nonneg)
        (fun i _ => mgf_le_of_lintegral_exp_abs_le_two (hX i).aemeasurable (K i) (hK i)
          (hmean i) (hpsi i) (hdomain i))
    _ = Real.exp (∑ i, 16 * K i ^ 2 * s ^ 2) := (Real.exp_sum _ _).symm
    _ = Real.exp (16 * (∑ i, K i ^ 2) * s ^ 2) := by
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- **Chernoff bound from a local quadratic CGF estimate.** If `cgf Y l ≤ C l² v` and
`e^{lY}` is integrable for `|l| ≤ (2Cb)⁻¹`, then for `t ≥ 0`
`P(Y ≥ t) ≤ exp(-(1/(4C)) min(t²/v, t/b))`. Vershynin 2018, proof of Theorem 2.8.1 (Chernoff
step, sub-exponential regime); atlas `hanson-wright`, `bernstein-scalar` (tail step). Ported from
Ported from HighDimProb (Zhang–Lee–Liu, Apache-2.0). -/
theorem measureReal_ge_le_exp_of_cgf_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} {v b C t : ℝ} (hC : 0 < C) (hv : 0 < v)
    (hb : 0 < b)
    (hcgf : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ → cgf Y μ l ≤ C * l ^ 2 * v)
    (hint : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * Y ω)) μ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ Y ω} ≤
      exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · calc μ.real {ω | 0 ≤ Y ω}
      _ ≤ (1 : ℝ) := ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      _ = exp (-(1 / (4 * C)) * min (0 ^ 2 / v) (0 / b)) := by simp
  · set l : ℝ := min (t / (2 * C * v)) ((2 * C * b)⁻¹) with hl_def
    have hden_v : 0 < 2 * C * v := by positivity
    have hden_b : 0 < 2 * C * b := by positivity
    have hl_nonneg : 0 ≤ l := by
      rw [hl_def]
      exact le_min (div_nonneg ht (le_of_lt hden_v)) (inv_nonneg.mpr (le_of_lt hden_b))
    have hl_domain : |l| ≤ (2 * C * b)⁻¹ := by
      rw [abs_of_nonneg hl_nonneg, hl_def]
      exact min_le_right _ _
    have hl_le_v : l ≤ t / (2 * C * v) := by
      rw [hl_def]
      exact min_le_left _ _
    have hl_mul_le_t : l * (2 * C * v) ≤ t := by
      rwa [le_div_iff₀ hden_v] at hl_le_v
    have hquad_le : C * l ^ 2 * v ≤ l * t / 2 := by
      nlinarith [hl_mul_le_t, hl_nonneg, hC.le, hv.le]
    have h_exp_to_half : -l * t + C * l ^ 2 * v ≤ -(l * t / 2) := by
      linarith
    have h_rate :
        l * t / 2 = (1 / (4 * C)) * min (t ^ 2 / v) (t / b) := by
      by_cases hcase : t / (2 * C * v) ≤ (2 * C * b)⁻¹
      · have htb_le_v : t * b ≤ v := by
          rw [inv_eq_one_div] at hcase
          rw [div_le_div_iff₀ hden_v hden_b] at hcase
          nlinarith [hcase, hC, hb]
        have hmin : min (t ^ 2 / v) (t / b) = t ^ 2 / v := by
          rw [min_eq_left]
          rw [div_le_div_iff₀ hv hb]
          nlinarith [htb_le_v, ht_pos]
        rw [hl_def, min_eq_left hcase, hmin]
        field_simp [hC.ne', hv.ne']
        ring
      · have hcase' : (2 * C * b)⁻¹ ≤ t / (2 * C * v) := le_of_not_ge hcase
        have hv_le_tb : v ≤ t * b := by
          rw [inv_eq_one_div] at hcase'
          rw [div_le_div_iff₀ hden_b hden_v] at hcase'
          nlinarith [hcase', hC, hv]
        have hmin : min (t ^ 2 / v) (t / b) = t / b := by
          rw [min_eq_right]
          rw [div_le_div_iff₀ hb hv]
          nlinarith [hv_le_tb, ht_pos]
        rw [hl_def, min_eq_right hcase', hmin]
        field_simp [hC.ne', hb.ne']
        ring
    have h_chernoff : μ.real {ω | t ≤ Y ω} ≤ exp (-l * t + cgf Y μ l) :=
      measure_ge_le_exp_cgf t hl_nonneg (hint l hl_domain)
    calc μ.real {ω | t ≤ Y ω}
      _ ≤ exp (-l * t + cgf Y μ l) := h_chernoff
      _ ≤ exp (-l * t + C * l ^ 2 * v) := by
        exact exp_le_exp.mpr (by linarith [hcgf l hl_domain])
      _ ≤ exp (-(l * t / 2)) := exp_le_exp.mpr h_exp_to_half
      _ = exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
        rw [h_rate]
        ring_nf

/-- **Two-sided Chernoff bound from a local quadratic CGF estimate.** Under the hypotheses of
`measureReal_ge_le_exp_of_cgf_le`, `P(|Y| ≥ t) ≤ 2 exp(-(1/(4C)) min(t²/v, t/b))` for `t ≥ 0`.
Vershynin 2018, proof of Theorem 2.8.1; atlas `hanson-wright`, `bernstein-scalar` (tail step).
Ported from HighDimProb (Zhang–Lee–Liu, Apache-2.0). -/
theorem measureReal_abs_ge_le_two_mul_exp_of_cgf_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {v b C t : ℝ} (hC : 0 < C) (hv : 0 < v) (hb : 0 < b)
    (hcgf : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ → cgf Y μ l ≤ C * l ^ 2 * v)
    (hint : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * Y ω)) μ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |Y ω|} ≤
      2 * exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
  have hpos := measureReal_ge_le_exp_of_cgf_le hC hv hb hcgf hint ht
  have hcgf_neg :
      ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
        cgf (fun ω => -Y ω) μ l ≤ C * l ^ 2 * v := by
    intro l hl
    have h_eq : cgf (fun ω => -Y ω) μ l = cgf Y μ (-l) := by
      unfold cgf mgf
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      congr 1
      ring
    rw [h_eq]
    have hl' : |-l| ≤ (2 * C * b)⁻¹ := by simpa [abs_neg] using hl
    simpa using hcgf (-l) hl'
  have hint_neg : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * (-Y ω))) μ := by
    intro l hl
    convert hint (-l) (by simpa [abs_neg] using hl) using 1
    ext ω
    ring_nf
  have hneg := measureReal_ge_le_exp_of_cgf_le hC hv hb hcgf_neg hint_neg ht
  have h_subset :
      {ω | t ≤ |Y ω|} ⊆ {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_or_gt 0 (Y ω) with hY | hY
    · left
      simpa [abs_of_nonneg hY] using hω
    · right
      simpa [abs_of_neg hY] using hω
  calc (μ {ω | t ≤ |Y ω|}).toReal
      ≤ (μ ({ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω})).toReal := by
        exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)
    _ ≤ (μ {ω | t ≤ Y ω}).toReal + (μ {ω | t ≤ -Y ω}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)
          (measure_union_le _ _)
    _ ≤ exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) +
        exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
        exact add_le_add hpos hneg
    _ = 2 * exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by ring

/-- **Scalar Bernstein inequality from `ψ₁` exponential bounds.** For mutually
independent centered real coordinates with positive scales satisfying
`E exp(|Xᵢ|/Kᵢ)≤2`, and any positive `B` dominating those scales,
`P(|ΣXᵢ|≥t)≤2exp(-min(t²/ΣKᵢ²,t/B)/64)` for `t≥0`.
The family may be empty; all moment and exponential-integrability conditions are derived.
Vershynin 2018, Theorem 2.8.4; atlas `bernstein-scalar`.
atlas: bernstein-scalar -/
theorem bernstein_sum_of_lintegral_exp_abs_le_two
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (K : ι → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hK : ∀ i, 0 < K i) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hpsi : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|X i ω| / K i)) ∂μ ≤ 2)
    (B : ℝ) (hB : 0 < B) (hKB : ∀ i, K i ≤ B) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(1 / 64 : ℝ) * min (t ^ 2 / (∑ i, K i ^ 2)) (t / B)) := by
  classical
  let V := ∑ i, K i ^ 2
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  show μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(1 / 64 : ℝ) * min (t ^ 2 / V) (t / B))
  rcases hV0.eq_or_lt with hVz | hV
  · have hVeq : V = 0 := hVz.symm
    rw [hVeq, div_zero, min_eq_left (by positivity : (0 : ℝ) ≤ t / B)]
    norm_num
    have hm : μ.real {ω | t ≤ |∑ i, X i ω|} ≤ 1 := by
      simpa [measureReal_def] using
        (measureReal_mono (μ := μ) (Set.subset_univ {ω | t ≤ |∑ i, X i ω|}))
    linarith
  · have hint := fun s (hs : |s| ≤ 1 / (2 * B)) =>
      integrable_exp_mul_sum_of_lintegral_exp_abs_le_two X K hX hind hK hpsi B hKB s hs
    have hloc := fun s (hs : |s| ≤ 1 / (2 * B)) =>
      mgf_sum_le_of_lintegral_exp_abs_le_two X K hX hind hK hmean hpsi B hKB s hs
    have hdom : ∀ l : ℝ, |l| ≤ (2 * 16 * (B / 16))⁻¹ → |l| ≤ 1 / (2 * B) := by
      intro l hl
      convert hl using 1
      field_simp
    have htail := measureReal_abs_ge_le_two_mul_exp_of_cgf_le
      (Y := fun ω => ∑ i, X i ω) (C := 16) (v := V) (b := B / 16)
      (by norm_num) hV (by positivity)
      (fun l hl => by
        calc cgf (fun ω => ∑ i, X i ω) μ l
            ≤ Real.log (Real.exp (16 * V * l ^ 2)) :=
              Real.log_le_log (mgf_pos (hint l (hdom l hl))) (hloc l (hdom l hl))
          _ = 16 * l ^ 2 * V := by rw [Real.log_exp]; ring)
      (fun l hl => hint l (hdom l hl)) ht
    refine htail.trans ?_
    gcongr 2 * Real.exp ?_
    have hmin : min (t ^ 2 / V) (t / B) ≤ min (t ^ 2 / V) (t / (B / 16)) := by
      refine min_le_min le_rfl ?_
      rw [div_div_eq_mul_div]
      exact div_le_div_of_nonneg_right (by nlinarith) hB.le
    have h64 : (1 : ℝ) / (4 * 16) = 1 / 64 := by norm_num
    rw [h64]
    nlinarith [hmin]

/-- Uniform-scale scalar Bernstein bound from `ψ₁` exponential moments:
`P(|ΣXᵢ|≥t)≤2exp(-min(t²/(N K²),t/K)/64)` for independent centered coordinates.
The bound also covers the empty family. Vershynin 2018, Theorem 2.8.4 (common-scale
corollary of `bernstein_sum_of_lintegral_exp_abs_le_two`). -/
theorem bernstein_sum_of_lintegral_exp_abs_le_two_uniform
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (K : ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hK : 0 < K) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hpsi : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|X i ω| / K)) ∂μ ≤ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(1 / 64 : ℝ) * min (t ^ 2 / ((Fintype.card ι : ℝ) * K ^ 2)) (t / K)) := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    bernstein_sum_of_lintegral_exp_abs_le_two X (fun _ => K) hX hind
      (fun _ => hK) hmean hpsi K hK (fun _ => le_rfl) t ht

end NLAlib
