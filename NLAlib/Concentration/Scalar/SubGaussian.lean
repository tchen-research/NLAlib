import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Convex.Integral
import NLAlib.Concentration.HansonWright.ExponentialSeries
import NLAlib.Concentration.HansonWright.LinearFormComparison
import NLAlib.Concentration.Scalar.Rademacher

/-!
# Sub-Gaussian moments, Khintchine and the maximal inequality

For `ProbabilityTheory.HasSubgaussianMGF X c μ` (Mathlib's sub-Gaussian predicate):

* `measure_lt_abs_le_of_hasSubgaussianMGF`: `P(t < |X|) ≤ 2 e^{-t²/(2c)}`;
* `integral_abs_rpow_le_of_hasSubgaussianMGF`: `𝔼|X|^p ≤ p (2c)^{p/2} Γ(p/2)` for real `p > 0`;
* `hasSubgaussianMGF_sum_mul_rademacher`, `integral_abs_rpow_sum_mul_rademacher_le`: Khintchine's
  inequality with an explicit constant (atlas `rademacher-khintchine`, upper half);
* `integral_iSup_le_of_hasSubgaussianMGF` and the `|·|` and `√(2c log N)` forms: the maximal
  inequality (atlas `subgaussian-max`), no independence needed;
* promoted (as `alias`es, proofs untouched) generic sub-Gaussian lemmas from the Hanson–Wright
  proof namespace `NLAlib.HansonWrightProof`.

Sources: Vershynin 2018, Prop 2.5.2, Thm 2.6.3, Ex 2.5.10; Boucheron–Lugosi–Massart 2013,
Thm 2.5. Audit G1 C6, C7, C9.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace NLAlib

private lemma integral_Ioi_two_mul_exp_mul_rpow {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => 2 * exp (-t ^ 2 / (2 * c)) * t ^ (p - 1)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), 2 * exp (-t ^ 2 / (2 * c)) * t ^ (p - 1) =
        (2 * c) ^ (p / 2) * Gamma (p / 2) := by
  have hb : (0 : ℝ) < 1 / (2 * c) := by positivity
  have hfun : (fun t : ℝ => 2 * exp (-t ^ 2 / (2 * c)) * t ^ (p - 1)) =
      fun t => 2 * (t ^ (p - 1) * exp (-(1 / (2 * c)) * t ^ (2 : ℝ))) := by
    funext t
    rw [rpow_two]
    ring_nf
  rw [hfun]
  refine ⟨(integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hb).const_mul 2, ?_⟩
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith) hb]
  have h1 : (p - 1 + 1) / 2 = p / 2 := by ring
  have h2 : -(p - 1 + 1) / 2 = -(p / 2) := by ring
  rw [h1, h2, one_div (2 * c), inv_rpow (by positivity), rpow_neg (by positivity), inv_inv]
  ring


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Two-sided sub-Gaussian tail: `P(t < |X|) ≤ 2 e^{-t²/(2c)}` for `t ≥ 0`.
Vershynin 2018, Prop 2.5.2 (i); atlas `rademacher-khintchine` (tail step). -/
theorem measure_lt_abs_le_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < |X ω|} ≤ ENNReal.ofReal (2 * exp (-t ^ 2 / (2 * c))) := by
  have hsub : {ω | t < |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ (-X) ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, Pi.neg_apply] at hω ⊢
    rcases le_or_gt 0 (X ω) with h0 | h0
    · left; rw [abs_of_nonneg h0] at hω; exact hω.le
    · right; rw [abs_of_neg h0] at hω; exact hω.le
  calc μ {ω | t < |X ω|} ≤ μ {ω | t ≤ X ω} + μ {ω | t ≤ (-X) ω} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (μ.real {ω | t ≤ X ω}) + ENNReal.ofReal (μ.real {ω | t ≤ (-X) ω}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (exp (-t ^ 2 / (2 * c))) + ENNReal.ofReal (exp (-t ^ 2 / (2 * c))) :=
        add_le_add (ENNReal.ofReal_le_ofReal (h.measure_ge_le ht))
          (ENNReal.ofReal_le_ofReal (h.neg.measure_ge_le ht))
    _ = ENNReal.ofReal (2 * exp (-t ^ 2 / (2 * c))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- **Sub-Gaussian absolute moments.** If `X` is sub-Gaussian with variance proxy `c`, then for
every real `p > 0`, `𝔼|X|^p ≤ p (2c)^{p/2} Γ(p/2)`. No integrability hypothesis is needed (the
bound shows `|X|^p` is integrable; the Bochner integral is used). For `c = 0` both sides vanish.
Vershynin 2018, Prop 2.5.2, proof of (i) ⇒ (ii) (layer-cake formula and the Gamma integral);
audit G1 C6. Atlas `rademacher-khintchine` (moment step); the atlas's unspecified `C_p` is
replaced by this explicit constant. -/
theorem integral_abs_rpow_le_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) {p : ℝ} (hp : 0 < p) :
    ∫ ω, |X ω| ^ p ∂μ ≤ p * (2 * c) ^ (p / 2) * Gamma (p / 2) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · have h0 := h.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hint : ∫ ω, |X ω| ^ p ∂μ = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      filter_upwards [h0] with ω hω
      simp [hω, zero_rpow hp.ne']
    rw [hint, NNReal.coe_zero, mul_zero, zero_rpow (by positivity), mul_zero, zero_mul]
  have hc : (0 : ℝ) < c := lt_of_le_of_ne c.2 (by exact_mod_cast hc0.symm)
  obtain ⟨hI, hval⟩ := integral_Ioi_two_mul_exp_mul_rpow hc hp
  have hXm : AEMeasurable (fun ω => |X ω|) μ := h.aemeasurable.abs
  have hlin : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ ≤
      ENNReal.ofReal (p * ((2 * c) ^ (p / 2) * Gamma (p / 2))) := by
    rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all _ fun ω => abs_nonneg (X ω)) hXm hp,
      ENNReal.ofReal_mul hp.le, ← hval,
      ofReal_integral_eq_lintegral_ofReal hI (ae_restrict_of_forall_mem measurableSet_Ioi
        fun t (ht : 0 < t) => by positivity)]
    gcongr 1
    refine setLIntegral_mono' measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_left (measure_lt_abs_le_of_hasSubgaussianMGF h ht.le) _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => by positivity)
    (hXm.pow_const p).aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ).toReal
      ≤ p * ((2 * c) ^ (p / 2) * Gamma (p / 2)) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
    _ = _ := by ring


/-! ### Promoted sub-Gaussian API from the Hanson–Wright proof -/

/-- A random variable with a sub-Gaussian MGF bound (for every real `t`) is centred:
`𝔼 X = 0`. Vershynin 2018, Prop 2.5.2 (v) ⇒ mean zero; atlas `hanson-wright` (helper).
Promoted from `HansonWrightProof.hasSubgaussianMGF_integral_eq_zero`. -/
alias integral_eq_zero_of_hasSubgaussianMGF := HansonWrightProof.hasSubgaussianMGF_integral_eq_zero

/-- Even moments of a sub-Gaussian variable: for every scale `s > 0`,
`𝔼 X^{2m} ≤ (2m)!/s^{2m} · e^{c s²/2}`. Vershynin 2018, Prop 2.5.2 (moment step);
atlas `hanson-wright` (helper). Promoted from
`HansonWrightProof.integral_even_power_le_of_hasSubgaussianMGF`. -/
alias integral_pow_two_mul_le_of_hasSubgaussianMGF :=
  HansonWrightProof.integral_even_power_le_of_hasSubgaussianMGF

/-- Exponential-square bound: if `X` is sub-Gaussian with proxy `c ≤ C₀` and
`θ C₀ e < 1`, then `𝔼 e^{θ X²} ≤ e (1 - θ C₀ e)⁻¹`. Vershynin 2018, Prop 2.5.2 (iii);
atlas `hanson-wright` (helper). Promoted from
`HansonWrightProof.integral_exp_mul_sq_le_inv_of_hasSubgaussianMGF_of_le`. -/
alias integral_exp_mul_sq_le_of_hasSubgaussianMGF :=
  HansonWrightProof.integral_exp_mul_sq_le_inv_of_hasSubgaussianMGF_of_le

/-- Monotonicity in the variance proxy: `HasSubgaussianMGF X c μ` and `c ≤ d` give
`HasSubgaussianMGF X d μ`. Atlas `hanson-wright` (helper). Promoted from
`HansonWrightProof.hasSubgaussianMGF_mono_param`. -/
alias hasSubgaussianMGF_mono := HansonWrightProof.hasSubgaussianMGF_mono_param

/-- A finite linear combination `∑_{i ∈ s} aᵢ Xᵢ` of independent sub-Gaussian variables is
sub-Gaussian with proxy `∑_{i ∈ s} aᵢ² cᵢ`. Vershynin 2018, Prop 2.6.1; atlas `hanson-wright`
(helper). Promoted from `HansonWrightProof.hasSubgaussianMGF_finset_sum_const_mul_of_iIndepFun`. -/
alias hasSubgaussianMGF_finset_sum_mul_of_iIndepFun :=
  HansonWrightProof.hasSubgaussianMGF_finset_sum_const_mul_of_iIndepFun

/-! ### Khintchine's inequality with an explicit constant -/

/-- A Rademacher series `∑ᵢ aᵢ εᵢ` with independent Rademacher signs is sub-Gaussian with
proxy `a ⬝ᵥ a = ∑ᵢ aᵢ²`. Vershynin 2018, Prop 2.6.1 with Example 2.5.8(ii);
atlas `rademacher-khintchine` (sub-Gaussian step). -/
theorem hasSubgaussianMGF_sum_mul_rademacher {ι : Type*} [Fintype ι] [IsProbabilityMeasure μ]
    (a : ι → ℝ) (ε : ι → Ω → ℝ) (hind : iIndepFun ε μ) (hlaw : ∀ i, IsRademacher μ (ε i)) :
    HasSubgaussianMGF (fun ω => ∑ i, a i * ε i ω) ⟨a ⬝ᵥ a, by
      simpa [dotProduct, ← sq] using Finset.sum_nonneg fun i _ => sq_nonneg (a i)⟩ μ := by
  have h := hasSubgaussianMGF_finset_sum_mul_of_iIndepFun hind (c := fun _ => 1)
    (s := Finset.univ) (fun i _ => hasSubgaussianMGF_of_isRademacher (hlaw i)) a
  refine (congrArg (fun c : ℝ≥0 => HasSubgaussianMGF (fun ω => ∑ i, a i * ε i ω) c μ) ?_).mp h
  ext
  simp [dotProduct, ← sq, Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

/-- **Khintchine's inequality, explicit constant.** For independent Rademacher signs `εᵢ` and
real `p > 0`, `𝔼|∑ᵢ aᵢ εᵢ|^p ≤ p (2 ‖a‖²)^{p/2} Γ(p/2)`, i.e. `‖∑ aᵢεᵢ‖_{L^p} ≤ C_p ‖a‖₂`
with `C_p = (p Γ(p/2))^{1/p} √2`. Vershynin 2018, Thm 2.6.3 / Ex 2.6.5 with the moment
constant of Prop 2.5.2; audit G1 C6. Atlas `rademacher-khintchine` (upper half). Deviation:
the atlas's unspecified `C_p` is replaced by this explicit constant; index type any
`[Fintype ι]`. -/
theorem integral_abs_rpow_sum_mul_rademacher_le {ι : Type*} [Fintype ι]
    [IsProbabilityMeasure μ] (a : ι → ℝ) (ε : ι → Ω → ℝ) (hind : iIndepFun ε μ)
    (hlaw : ∀ i, IsRademacher μ (ε i)) {p : ℝ} (hp : 0 < p) :
    ∫ ω, |∑ i, a i * ε i ω| ^ p ∂μ ≤ p * (2 * (a ⬝ᵥ a)) ^ (p / 2) * Gamma (p / 2) :=
  integral_abs_rpow_le_of_hasSubgaussianMGF (hasSubgaussianMGF_sum_mul_rademacher a ε hind hlaw) hp

/-! ### Maximal inequality -/

private lemma integral_le_log_div_of_integral_exp_le [IsProbabilityMeasure μ] {M : Ω → ℝ}
    (hM : Integrable M μ) {s B : ℝ} (hs : 0 < s)
    (hexp : Integrable (fun ω => exp (s * M ω)) μ) (hB : ∫ ω, exp (s * M ω) ∂μ ≤ B) :
    ∫ ω, M ω ∂μ ≤ log B / s := by
  have hJ : exp (∫ ω, s * M ω ∂μ) ≤ ∫ ω, exp (s * M ω) ∂μ :=
    convexOn_exp.map_integral_le continuousOn_exp isClosed_univ (ae_of_all _ fun _ => trivial)
      (hM.const_mul s) hexp
  rw [integral_const_mul] at hJ
  have hBpos : 0 < B := (exp_pos _).trans_le (hJ.trans hB)
  rw [le_div_iff₀ hs, mul_comm]
  exact (le_log_iff_exp_le hBpos).2 (hJ.trans hB)

private lemma exists_eq_iSup_fintype {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    ∃ j, f j = ⨆ i, f i := exists_eq_ciSup_of_finite

private lemma abs_iSup_le_sum_abs {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    |⨆ i, f i| ≤ ∑ i, |f i| := by
  obtain ⟨j, hj⟩ := exists_eq_iSup_fintype f
  rw [← hj]
  exact Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

/-- Shared skeleton of the maximal inequalities: `M ω = ⨆ᵢ Yᵢ ω` is integrable, and if
`e^{sM} ≤ ∑ₖ Fₖ` pointwise with `∫ Fₖ ≤ b`, then `𝔼 M ≤ log(K b)/s`. -/
private lemma integral_iSup_le_aux [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι]
    [Nonempty ι] [Fintype κ] (Y : ι → Ω → ℝ) (hY : ∀ i, Integrable (Y i) μ)
    (F : κ → Ω → ℝ) (hF : ∀ k, Integrable (F k) μ) {s b : ℝ} (hs : 0 < s)
    (hexp : ∀ ω, exp (s * ⨆ i, Y i ω) ≤ ∑ k, F k ω) (hb : ∀ k, ∫ ω, F k ω ∂μ ≤ b) :
    Integrable (fun ω => ⨆ i, Y i ω) μ ∧
      ∫ ω, ⨆ i, Y i ω ∂μ ≤ log (Fintype.card κ * b) / s := by
  have hm : AEMeasurable (fun ω => ⨆ i, Y i ω) μ :=
    AEMeasurable.iSup fun i => (hY i).aemeasurable
  have hint : Integrable (fun ω => ⨆ i, Y i ω) μ :=
    (integrable_finsetSum Finset.univ fun i _ => (hY i).abs).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs, Finset.sum_apply] using abs_iSup_le_sum_abs (Y · ω))
  have hsum : Integrable (fun ω => ∑ k, F k ω) μ := integrable_finsetSum Finset.univ fun k _ => hF k
  have hexpint : Integrable (fun ω => exp (s * ⨆ i, Y i ω)) μ :=
    hsum.mono' (measurable_exp.comp_aemeasurable (hm.const_mul s)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact hexp ω)
  refine ⟨hint, integral_le_log_div_of_integral_exp_le hint hs hexpint ?_⟩
  calc ∫ ω, exp (s * ⨆ i, Y i ω) ∂μ ≤ ∫ ω, ∑ k, F k ω ∂μ :=
        integral_mono hexpint hsum hexp
    _ = ∑ k, ∫ ω, F k ω ∂μ := integral_finsetSum _ fun k _ => hF k
    _ ≤ ∑ _k : κ, b := Finset.sum_le_sum fun k _ => hb k
    _ = Fintype.card κ * b := by simp

/-- **Sub-Gaussian maximal inequality.** If each `Xᵢ` (finitely many, no independence needed)
is sub-Gaussian with proxy `c`, then `⨆ᵢ Xᵢ` is integrable and for every `s > 0`,
`𝔼 maxᵢ Xᵢ ≤ log N / s + c s / 2` with `N = card ι`.
Boucheron–Lugosi–Massart 2013, Thm 2.5 (proof); Vershynin 2018, Ex 2.5.10; audit G1 C7.
Atlas `subgaussian-max`. -/
theorem integral_iSup_le_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    [Nonempty ι] (X : ι → Ω → ℝ) (c : ℝ≥0) (h : ∀ i, HasSubgaussianMGF (X i) c μ) {s : ℝ}
    (hs : 0 < s) :
    Integrable (fun ω => ⨆ i, X i ω) μ ∧
      ∫ ω, ⨆ i, X i ω ∂μ ≤ log (Fintype.card ι) / s + c * s / 2 := by
  have hexp : ∀ ω, exp (s * ⨆ i, X i ω) ≤ ∑ i, exp (s * X i ω) := by
    intro ω
    obtain ⟨j, hj⟩ := exists_eq_iSup_fintype (X · ω)
    rw [← hj]
    exact Finset.single_le_sum (f := fun i => exp (s * X i ω)) (fun i _ => (exp_pos _).le)
      (Finset.mem_univ j)
  obtain ⟨hint, hle⟩ := integral_iSup_le_aux X (fun i => (h i).integrable)
    (fun i ω => exp (s * X i ω)) (fun i => (h i).integrable_exp_mul s) hs hexp
    (fun i => (h i).mgf_le s)
  refine ⟨hint, hle.trans_eq ?_⟩
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [log_mul hN.ne' (exp_pos _).ne', log_exp, add_div]
  congr 1
  field_simp

/-- **Sub-Gaussian maximal inequality, absolute values.** Under the hypotheses of
`integral_iSup_le_of_hasSubgaussianMGF`, `⨆ᵢ |Xᵢ|` is integrable and for every `s > 0`,
`𝔼 maxᵢ |Xᵢ| ≤ log (2N) / s + c s / 2`. Boucheron–Lugosi–Massart 2013, Thm 2.5 (applied to
`±Xᵢ`); Vershynin 2018, Ex 2.5.10; audit G1 C7. Atlas `subgaussian-max`. -/
theorem integral_iSup_abs_le_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (c : ℝ≥0) (h : ∀ i, HasSubgaussianMGF (X i) c μ)
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun ω => ⨆ i, |X i ω|) μ ∧
      ∫ ω, ⨆ i, |X i ω| ∂μ ≤ log (2 * Fintype.card ι) / s + c * s / 2 := by
  have hexp : ∀ ω, exp (s * ⨆ i, |X i ω|) ≤
      ∑ k : ι × Bool, exp ((if k.2 then s else -s) * X k.1 ω) := by
    intro ω
    obtain ⟨j, hj⟩ := exists_eq_iSup_fintype (fun i => |X i ω|)
    rw [← hj]
    have hj2 : exp (s * |X j ω|) ≤ ∑ b : Bool, exp ((if b then s else -s) * X j ω) := by
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      rcases le_or_gt 0 (X j ω) with h0 | h0
      · rw [abs_of_nonneg h0]; linarith [exp_pos (-s * X j ω)]
      · rw [abs_of_neg h0, mul_neg, ← neg_mul]; linarith [exp_pos (s * X j ω)]
    refine hj2.trans ?_
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun i => ∑ b : Bool, exp ((if b then s else -s) * X i ω))
      (fun i _ => Finset.sum_nonneg fun _ _ => (exp_pos _).le) (Finset.mem_univ j)
  have hb : ∀ k : ι × Bool, ∫ ω, exp ((if k.2 then s else -s) * X k.1 ω) ∂μ ≤
      exp (c * s ^ 2 / 2) := by
    intro k
    have := (h k.1).mgf_le (if k.2 then s else -s)
    split_ifs at this ⊢ <;> simpa [mgf] using this
  obtain ⟨hint, hle⟩ := integral_iSup_le_aux (fun i ω => |X i ω|) (fun i => (h i).integrable.abs)
    (fun (k : ι × Bool) ω => exp ((if k.2 then s else -s) * X k.1 ω))
    (fun k => (h k.1).integrable_exp_mul _) hs hexp hb
  refine ⟨hint, hle.trans_eq ?_⟩
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, mul_comm _ (2 : ℝ),
    log_mul (by positivity) (exp_pos _).ne', log_exp, add_div]
  congr 1
  field_simp

private lemma le_sqrt_of_forall_le_div_add {x L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (h : ∀ s : ℝ, 0 < s → x ≤ L / s + c * s / 2) : x ≤ √(2 * c * L) := by
  rcases hL.eq_or_lt with rfl | hL'
  · rw [mul_zero, sqrt_zero]
    by_contra hx
    push Not at hx
    have := h (x / (c + 1)) (by positivity)
    rw [zero_div, zero_add] at this
    have h1 : c * (x / (c + 1)) / 2 < x := by
      rw [mul_div_assoc', div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases hc.eq_or_lt with rfl | hc'
  · rw [mul_zero, zero_mul, sqrt_zero]
    by_contra hx
    push Not at hx
    have := h (2 * L / x) (by positivity)
    rw [zero_mul, zero_div, add_zero, div_div_eq_mul_div] at this
    have h1 : L * x / (2 * L) = x / 2 := by field_simp
    linarith
  set r := √(2 * c * L) with hr
  have hr0 : 0 < r := sqrt_pos.2 (by positivity)
  have hr2 : r * r = 2 * c * L := mul_self_sqrt (by positivity)
  have := h (r / c) (by positivity)
  have h1 : L / (r / c) + c * (r / c) / 2 = r := by
    field_simp
    nlinarith
  linarith

/-- **Sub-Gaussian maximal inequality, optimised form**: `𝔼 maxᵢ Xᵢ ≤ √(2 c log N)` for
`N = card ι ≥ 1` sub-Gaussian variables with proxy `c` (no independence needed).
Boucheron–Lugosi–Massart 2013, Thm 2.5; Vershynin 2018, Ex 2.5.10; audit G1 C7.
Atlas `subgaussian-max`. -/
theorem integral_iSup_le_sqrt_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (c : ℝ≥0) (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, X i ω ∂μ ≤ √(2 * c * log (Fintype.card ι)) :=
  le_sqrt_of_forall_le_div_add (log_nonneg (by exact_mod_cast Fintype.card_pos)) c.2
    fun _ hs => (integral_iSup_le_of_hasSubgaussianMGF X c h hs).2

/-- **Sub-Gaussian maximal inequality, absolute values, optimised form**:
`𝔼 maxᵢ |Xᵢ| ≤ √(2 c log (2N))`. Boucheron–Lugosi–Massart 2013, Thm 2.5; Vershynin 2018,
Ex 2.5.10; audit G1 C7. Atlas `subgaussian-max`. -/
theorem integral_iSup_abs_le_sqrt_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (c : ℝ≥0) (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, |X i ω| ∂μ ≤ √(2 * c * log (2 * Fintype.card ι)) :=
  le_sqrt_of_forall_le_div_add
    (log_nonneg (by have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
                    linarith)) c.2
    fun _ hs => (integral_iSup_abs_le_of_hasSubgaussianMGF X c h hs).2

end NLAlib
