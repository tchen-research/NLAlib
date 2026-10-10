import NLAlib.Concentration.OrliczMGF
import Mathlib.Probability.Independence.Integration

/-!
# Scalar Bernstein inequality from genuine Orlicz bounds

Independent centered coordinates satisfying `E exp(|Xᵢ|/Kᵢ) ≤ 2` obey
`P(|Σ Xᵢ| ≥ t) ≤ 2 exp(-min(t²/Σ Kᵢ², t/B)/64)`, where `B>0` dominates the scales.
All moments and local exponential integrability are derived from the nonnegative Orlicz
expectations. The sum may be empty. The constant `1/64` is conservative.

Vershynin 2018, Theorem 2.8.4; atlas `bernstein-scalar`.
The independent-MGF factorization is Mathlib's theorem; no HighDimProb dependency is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

/-- Independent genuine `ψ₁` bounds give the local MGF bound for the sum, with quadratic
proxy `16ΣKᵢ²` and radius `1/(2B)`. Exponential integrability is included in the conclusion.
Vershynin 2018, proof of Theorem 2.8.4; atlas `bernstein-scalar` (MGF assembly). -/
theorem integrable_and_local_mgf_sum_le_of_lintegral_exp_abs_le_two
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (K : ι → ℝ)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hK : ∀ i, 0 < K i) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hpsi : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|X i ω| / K i)) ∂μ ≤ 2)
    (B : ℝ) (_hB : 0 < B) (hKB : ∀ i, K i ≤ B) (s : ℝ) (hs : |s| ≤ 1 / (2 * B)) :
    Integrable (fun ω => Real.exp (s * ∑ i, X i ω)) μ ∧
      mgf (fun ω => ∑ i, X i ω) μ s ≤ Real.exp (16 * (∑ i, K i ^ 2) * s ^ 2) := by
  classical
  have hdomain : ∀ i, |s| ≤ 1 / (2 * K i) := fun i => hs.trans
    (one_div_le_one_div_of_le (mul_pos (by norm_num) (hK i)) (by nlinarith [hKB i]))
  have hf := fun i => integrable_and_local_mgf_le_of_lintegral_exp_abs_le_two
    (hX i).aemeasurable (K i) (hK i) (hmean i) (hpsi i)
  have hexp : Integrable (fun ω => Real.exp (s * ∑ i, X i ω)) μ := by
    simpa only [Finset.sum_apply] using hindep.integrable_exp_mul_sum
      (t := s) hX (s := Finset.univ) (fun i _ => ((hf i).2 s (hdomain i)).1)
  refine ⟨hexp, ?_⟩
  have heq : mgf (fun ω => ∑ i, X i ω) μ s = ∏ i, mgf (X i) μ s := by
    have hfun : (∑ i, X i) = fun ω => ∑ i, X i ω := by
      funext ω
      simp only [Finset.sum_apply]
    rw [← hfun]
    exact hindep.mgf_sum (t := s) hX Finset.univ
  rw [heq]
  calc
    ∏ i, mgf (X i) μ s ≤ ∏ i, Real.exp (16 * K i ^ 2 * s ^ 2) :=
      Finset.prod_le_prod (fun _ _ => mgf_nonneg)
        (fun i _ => ((hf i).2 s (hdomain i)).2)
    _ = Real.exp (∑ i, 16 * K i ^ 2 * s ^ 2) := (Real.exp_sum _ _).symm
    _ = Real.exp (16 * (∑ i, K i ^ 2) * s ^ 2) := by
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- A local MGF bound `mgf(s)≤exp(16Vs²)` for `|s|≤1/(2B)`, including tilt
integrability, gives the upper Bernstein tail with constant `1/64`.
Vershynin 2018, Theorem 2.8.4 (Chernoff step); atlas `bernstein-scalar`. -/
theorem measureReal_ge_le_bernstein_of_local_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Ω → ℝ}
    (V B : ℝ) (hV : 0 < V) (hB : 0 < B)
    (hlocal : ∀ s : ℝ, |s| ≤ 1 / (2 * B) →
      Integrable (fun ω => Real.exp (s * S ω)) μ ∧ mgf S μ s ≤ Real.exp (16 * V * s ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ S ω} ≤ Real.exp (-(1 / 64 : ℝ) * min (t ^ 2 / V) (t / B)) := by
  let s := min (t / (32 * V)) (1 / (32 * B))
  have hs0 : 0 ≤ s := le_min (by positivity) (by positivity)
  have hsV : s ≤ t / (32 * V) := min_le_left _ _
  have hsB : s ≤ 1 / (32 * B) := min_le_right _ _
  have hsdom : |s| ≤ 1 / (2 * B) := by
    rw [abs_of_nonneg hs0]
    exact hsB.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))
  obtain ⟨hexp, hmgf⟩ := hlocal s hsdom
  have htV : s * (32 * V) ≤ t := (le_div_iff₀ (by positivity)).mp hsV
  have hexponent : -s * t + 16 * V * s ^ 2 ≤ -(s * t / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left htV hs0]
  have hrate : s * t / 2 = (1 / 64 : ℝ) * min (t ^ 2 / V) (t / B) := by
    dsimp [s]
    rw [mul_div_assoc, min_mul_of_nonneg _ _ (by positivity : 0 ≤ t / 2)]
    have h1 : t / (32 * V) * (t / 2) = (1 / 64 : ℝ) * (t ^ 2 / V) := by ring
    have h2 : 1 / (32 * B) * (t / 2) = (1 / 64 : ℝ) * (t / B) := by ring
    rw [h1, h2, ← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 64)]
  calc
    μ.real {ω | t ≤ S ω} ≤ Real.exp (-s * t) * mgf S μ s :=
      measure_ge_le_exp_mul_mgf t hs0 hexp
    _ ≤ Real.exp (-s * t) * Real.exp (16 * V * s ^ 2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-s * t + 16 * V * s ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(s * t / 2)) := Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [hrate]; congr 1; ring

/-- A symmetric local MGF bound `mgf(s)≤exp(16Vs²)` for `|s|≤1/(2B)`, including
tilt integrability, gives the two-sided Bernstein tail with constant `1/64`.
Vershynin 2018, Theorem 2.8.4 (Chernoff step); atlas `bernstein-scalar`. -/
theorem measureReal_abs_ge_le_bernstein_of_local_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Ω → ℝ}
    (V B : ℝ) (hV : 0 < V) (hB : 0 < B)
    (hlocal : ∀ s : ℝ, |s| ≤ 1 / (2 * B) →
      Integrable (fun ω => Real.exp (s * S ω)) μ ∧ mgf S μ s ≤ Real.exp (16 * V * s ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |S ω|} ≤ 2 * Real.exp (-(1 / 64 : ℝ) * min (t ^ 2 / V) (t / B)) := by
  have hupper := measureReal_ge_le_bernstein_of_local_mgf V B hV hB hlocal t ht
  have hneg : ∀ s : ℝ, |s| ≤ 1 / (2 * B) →
      Integrable (fun ω => Real.exp (s * (-S ω))) μ ∧
        mgf (fun ω => -S ω) μ s ≤ Real.exp (16 * V * s ^ 2) := by
    intro s hs
    simpa only [mgf, neg_mul, mul_neg, neg_sq] using hlocal (-s) (by simpa using hs)
  have hlower := measureReal_ge_le_bernstein_of_local_mgf V B hV hB hneg t ht
  have hsub : {ω | t ≤ |S ω|} ⊆ {ω | t ≤ S ω} ∪ {ω | t ≤ -S ω} := by
    intro ω hω
    change t ≤ |S ω| at hω
    by_cases hS : 0 ≤ S ω
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq, abs_of_nonneg hS] using hω)
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq, abs_of_neg (not_le.mp hS)] using hω)
  calc
    μ.real {ω | t ≤ |S ω|} ≤ μ.real ({ω | t ≤ S ω} ∪ {ω | t ≤ -S ω}) :=
      measureReal_mono hsub
    _ ≤ μ.real {ω | t ≤ S ω} + μ.real {ω | t ≤ -S ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(1 / 64 : ℝ) * min (t ^ 2 / V) (t / B)) := by linarith

/-- **Scalar Bernstein inequality from genuine `ψ₁` exponential bounds.** For mutually
independent centered real coordinates with positive scales satisfying
`E exp(|Xᵢ|/Kᵢ)≤2`, and any positive `B` dominating those scales,
`P(|ΣXᵢ|≥t)≤2exp(-min(t²/ΣKᵢ²,t/B)/64)` for `t≥0`.
The family may be empty; all moment and exponential-integrability conditions are derived.
Vershynin 2018, Theorem 2.8.4; atlas `bernstein-scalar`. -/
theorem bernstein_sum_of_lintegral_exp_abs_le_two
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (K : ι → ℝ)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hK : ∀ i, 0 < K i) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hpsi : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|X i ω| / K i)) ∂μ ≤ 2)
    (B : ℝ) (hB : 0 < B) (hKB : ∀ i, K i ≤ B) (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 64 : ℝ) *
        min (t ^ 2 / (∑ i, K i ^ 2)) (t / B))) := by
  classical
  let V := ∑ i, K i ^ 2
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hreal : μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(1 / 64 : ℝ) * min (t ^ 2 / V) (t / B)) := by
    rcases hV0.eq_or_lt with hVz | hV
    · have hVeq : V = 0 := hVz.symm
      rw [hVeq, div_zero, min_eq_left (by positivity : (0 : ℝ) ≤ t / B)]
      norm_num
      have hm : μ.real {ω | t ≤ |∑ i, X i ω|} ≤ 1 := by
        simpa [measureReal_def] using
          (measureReal_mono (μ := μ) (Set.subset_univ {ω | t ≤ |∑ i, X i ω|}))
      linarith
    · exact measureReal_abs_ge_le_bernstein_of_local_mgf V B hV hB
        (fun s hs => integrable_and_local_mgf_sum_le_of_lintegral_exp_abs_le_two
          X K hX hindep hK hmean hpsi B hB hKB s hs) t ht
  rw [← ofReal_measureReal (μ := μ)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Uniform-scale scalar Bernstein bound from genuine `ψ₁` exponential moments:
`P(|ΣXᵢ|≥t)≤2exp(-min(t²/(N K²),t/K)/64)` for independent centered coordinates.
The bound also covers the empty family. Vershynin 2018, Theorem 2.8.4;
atlas `bernstein-scalar` (common-scale corollary). -/
theorem bernstein_sum_of_lintegral_exp_abs_le_two_uniform
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (K : ℝ)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hK : 0 < K) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hpsi : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|X i ω| / K)) ∂μ ≤ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 64 : ℝ) *
        min (t ^ 2 / ((Fintype.card ι : ℝ) * K ^ 2)) (t / K))) := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    bernstein_sum_of_lintegral_exp_abs_le_two X (fun _ => K) hX hindep
      (fun _ => hK) hmean hpsi K hK (fun _ => le_rfl) t ht

end NLAlib
