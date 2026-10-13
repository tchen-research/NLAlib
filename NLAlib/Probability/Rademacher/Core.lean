import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import NLAlib.ForMathlib.Probability.HasLaw
/-!
# The Rademacher law and the Rademacher vector

The Rademacher probability measure `rademacherMeasure = ½ δ₁ + ½ δ₋₁` on `ℝ`; a Rademacher sign
is `HasLaw r rademacherMeasure μ`, a vector of independent signs is
`HasLaw r (rademacherVector n) μ` with `rademacherVector n := Measure.pi fun _ => rademacherMeasure`.

* `hasLaw_rademacherMeasure_iff_map_eq`, `ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure`;
* `memLp_two_of_hasLaw_rademacherMeasure`, `integral_eq_zero_of_hasLaw_rademacherMeasure`,
  `integral_sq_eq_one_of_hasLaw_rademacherMeasure`, `integrable_pow_four_of_hasLaw_rademacherMeasure`,
  `integral_pow_four_eq_one_of_hasLaw_rademacherMeasure`, `integrable_exp_mul_of_hasLaw_rademacherMeasure`:
  moments of a Rademacher sign;
* `hasSubgaussianMGF_id_rademacherMeasure`, `hasSubgaussianMGF_of_hasLaw_rademacherMeasure`:
  a Rademacher sign is sub-Gaussian with variance proxy `1` (Hoeffding's lemma on `[-1, 1]`);
* `rademacherVector`, `hasLaw_eval_rademacherVector`, `iIndepFun_eval_rademacherVector`,
  `hasLaw_rademacherVector_of_iIndepFun`, `HasLaw.hasLaw_eval_rademacherMeasure`,
  `HasLaw.iIndepFun_eval_of_rademacherVector`.

Atlas: `scalar-laws-def`, `rademacher-khintchine` (sub-Gaussian half), `hutchinson-variance`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NLAlib

/-- The Rademacher probability measure, assigning mass one half to each of `1` and `-1`.
Vershynin 2018, Example 2.5.8(ii).
atlas: scalar-laws-def -/
def rademacherMeasure : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)

/-- The Rademacher measure has total mass one. -/
instance isProbabilityMeasure_rademacherMeasure : IsProbabilityMeasure rademacherMeasure := by
  constructor
  norm_num [rademacherMeasure]
  simpa only [one_div] using ENNReal.add_halves 1

/-- `r` is a Rademacher sign under `μ` exactly when `μ.map r = rademacherMeasure` (the law being a
probability measure forces a.e. measurability). -/
theorem hasLaw_rademacherMeasure_iff_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : Ω → ℝ} : HasLaw r rademacherMeasure μ ↔ μ.map r = rademacherMeasure :=
  hasLaw_iff_map_eq (IsProbabilityMeasure.ne_zero _)

/-- The Rademacher vector law on `n → ℝ`: the product of `n` independent Rademacher signs. An
`abbrev`, so that Mathlib's `Measure.pi` API applies directly. Vershynin 2018, §2.2.
atlas: scalar-laws-def -/
abbrev rademacherVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ => rademacherMeasure

/-- Each coordinate of the Rademacher vector is a Rademacher sign. -/
theorem hasLaw_eval_rademacherVector {n : Type*} [Fintype n] (i : n) :
    HasLaw (fun x : n → ℝ => x i) rademacherMeasure (rademacherVector n) :=
  (measurePreserving_eval (fun _ : n => rademacherMeasure) i).hasLaw

/-- The coordinates of the Rademacher vector are independent. -/
theorem iIndepFun_eval_rademacherVector (n : Type*) [Fintype n] :
    iIndepFun (fun (i : n) (x : n → ℝ) => x i) (rademacherVector n) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Independent Rademacher coordinates form a Rademacher vector. -/
theorem hasLaw_rademacherVector_of_iIndepFun {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype n] {x : n → Ω → ℝ} (hx : ∀ i, HasLaw (x i) rademacherMeasure μ)
    (hind : iIndepFun x μ) :
    HasLaw (fun ω i => x i ω) (rademacherVector n) μ :=
  hind.hasLaw_pi hx

/-- A coordinate of a Rademacher vector is a Rademacher sign. -/
theorem _root_.ProbabilityTheory.HasLaw.hasLaw_eval_rademacherMeasure {Ω n : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [Fintype n] {x : Ω → n → ℝ}
    (hx : HasLaw x (rademacherVector n) μ) (i : n) :
    HasLaw (fun ω => x ω i) rademacherMeasure μ :=
  (hasLaw_eval_rademacherVector i).comp hx

/-- The coordinates of a Rademacher vector are independent. -/
theorem _root_.ProbabilityTheory.HasLaw.iIndepFun_eval_of_rademacherVector {Ω n : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [Fintype n] {x : Ω → n → ℝ}
    (hx : HasLaw x (rademacherVector n) μ) :
    iIndepFun (fun i ω => x ω i) μ := by
  have := hx.isProbabilityMeasure
  exact (iIndepFun_iff_hasLaw_pi_pi (fun i => hx.hasLaw_eval_rademacherMeasure i)).2 hx

/-- Almost every point of the Rademacher law lies in `[-1, 1]`. -/
theorem ae_mem_Icc_rademacherMeasure : ∀ᵐ x ∂rademacherMeasure, x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  have hS : MeasurableSet {a : ℝ | ¬a ∈ Set.Icc (-1 : ℝ) 1} :=
    measurableSet_Icc.compl
  simp only [rademacherMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hS]
  norm_num

/-- Almost every point of the Rademacher law is `1` or `-1`. -/
theorem ae_eq_one_or_neg_one_rademacherMeasure :
    ∀ᵐ x ∂rademacherMeasure, x = 1 ∨ x = -1 := by
  have hS : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} :=
    (measurableSet_singleton 1).union (measurableSet_singleton (-1))
  rw [rademacherMeasure, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inl rfl)) _,
    Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inr rfl)) _⟩

/-- Every function is integrable against the two-point Rademacher law. -/
theorem integrable_rademacherMeasure (f : ℝ → ℝ) : Integrable f rademacherMeasure :=
  Integrable.add_measure (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))
    (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))

/-- The integral against the Rademacher law is the average of the values at `1` and `-1`. -/
theorem integral_rademacherMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂rademacherMeasure = (f 1 + f (-1)) / 2 := by
  have hi : ∀ a : ℝ, Integrable f ((1 / 2 : ENNReal) • Measure.dirac a) :=
    fun a => (integrable_dirac (by simp)).smul_measure (by simp)
  rw [rademacherMeasure, integral_add_measure (hi 1) (hi (-1)), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- The Rademacher law has mean zero. -/
theorem integral_id_rademacherMeasure : ∫ x, x ∂rademacherMeasure = 0 := by
  rw [integral_rademacherMeasure (fun x => x)]
  norm_num

/-- The moment generating function of the Rademacher law is `cosh`. -/
theorem mgf_id_rademacherMeasure (t : ℝ) : mgf id rademacherMeasure t = Real.cosh t := by
  rw [mgf, integral_rademacherMeasure (fun x => Real.exp (t * id x)), Real.cosh_eq]
  simp only [id_eq, mul_one, mul_neg]

/-- **The Rademacher law is `1`-sub-Gaussian**: `𝔼 e^{t ε} ≤ e^{t²/2}`.
Hoeffding's lemma on `[-1, 1]` (Mathlib `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`).
Vershynin 2018, Example 2.5.8(ii). -/
theorem hasSubgaussianMGF_id_rademacherMeasure : HasSubgaussianMGF id 1 rademacherMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := rademacherMeasure)
    (X := id) aemeasurable_id ae_mem_Icc_rademacherMeasure integral_id_rademacherMeasure
  convert h using 1
  ext
  norm_num

section HasLawRademacher

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {r : Ω → ℝ}

/-- **A Rademacher sign is `1`-sub-Gaussian**: `𝔼 e^{t r} ≤ e^{t²/2}` for every real `t`.
Vershynin 2018, Example 2.5.8(ii).
atlas: rademacher-khintchine -/
theorem hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hr : HasLaw r rademacherMeasure μ) :
    HasSubgaussianMGF r 1 μ := by
  rw [← HasSubgaussianMGF.id_map_iff hr.aemeasurable, hr.map_eq]
  exact hasSubgaussianMGF_id_rademacherMeasure

/-- A Rademacher sign is almost surely `1` or `-1`. -/
theorem ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure (hr : HasLaw r rademacherMeasure μ) :
    ∀ᵐ ω ∂μ, r ω = 1 ∨ r ω = -1 := by
  have hS : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} :=
    (measurableSet_singleton 1).union (measurableSet_singleton (-1))
  rw [← ae_map_iff hr.aemeasurable hS, hr.map_eq]
  exact ae_eq_one_or_neg_one_rademacherMeasure

/-- The mgf of a Rademacher sign is `cosh`. -/
theorem mgf_of_hasLaw_rademacherMeasure (hr : HasLaw r rademacherMeasure μ) (t : ℝ) :
    mgf r μ t = Real.cosh t := by
  rw [← mgf_id_rademacherMeasure, ← hr.map_eq, mgf_id_map hr.aemeasurable]

/-- A Rademacher sign is square integrable. -/
theorem memLp_two_of_hasLaw_rademacherMeasure (hr : HasLaw r rademacherMeasure μ) :
    MemLp r 2 μ :=
  have := hr.isProbabilityMeasure
  MemLp.of_bound hr.aemeasurable.aestronglyMeasurable 1
    ((ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure hr).mono fun ω h => by
      rcases h with h | h <;> simp [h])

/-- A Rademacher sign has mean zero. Hutchinson 1989; Avron–Toledo 2011, Lemma 6. -/
theorem integral_eq_zero_of_hasLaw_rademacherMeasure (hr : HasLaw r rademacherMeasure μ) :
    ∫ ω, r ω ∂μ = 0 := by
  have h := integral_map hr.aemeasurable (f := fun x : ℝ => x) aestronglyMeasurable_id
  rw [hr.map_eq, integral_id_rademacherMeasure] at h
  exact h.symm

/-- A Rademacher sign has second moment one. Avron–Toledo 2011, Lemma 6. -/
theorem integral_sq_eq_one_of_hasLaw_rademacherMeasure (hr : HasLaw r rademacherMeasure μ) :
    ∫ ω, r ω ^ 2 ∂μ = 1 := by
  have := hr.isProbabilityMeasure
  rw [integral_congr_ae ((ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure hr).mono
    fun ω h => by rcases h with h | h <;> simp [h] : ∀ᵐ ω ∂μ, r ω ^ 2 = (1 : ℝ))]
  simp

/-- The fourth power of a Rademacher sign is integrable. -/
theorem integrable_pow_four_of_hasLaw_rademacherMeasure (hr : HasLaw r rademacherMeasure μ) :
    Integrable (fun ω => r ω ^ 4) μ := by
  have := hr.isProbabilityMeasure
  exact (integrable_const (1 : ℝ)).congr
    ((ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure hr).mono fun ω h => by
      rcases h with h | h <;> norm_num [h])

/-- A Rademacher sign has fourth moment one. Avron–Toledo 2011, Lemma 6. -/
theorem integral_pow_four_eq_one_of_hasLaw_rademacherMeasure
    (hr : HasLaw r rademacherMeasure μ) :
    ∫ ω, r ω ^ 4 ∂μ = 1 := by
  have := hr.isProbabilityMeasure
  rw [integral_congr_ae ((ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure hr).mono
    fun ω h => by rcases h with h | h <;> norm_num [h] : ∀ᵐ ω ∂μ, r ω ^ 4 = (1 : ℝ))]
  simp

/-- A Rademacher sign has all exponential moments. -/
theorem integrable_exp_mul_of_hasLaw_rademacherMeasure (hr : HasLaw r rademacherMeasure μ)
    (c : ℝ) : Integrable (fun ω => Real.exp (c * r ω)) μ :=
  (hasSubgaussianMGF_of_hasLaw_rademacherMeasure hr).integrable_exp_mul c

end HasLawRademacher

/-- Every coordinate of a Rademacher vector squares to one almost surely. -/
theorem ae_forall_sq_eq_one_rademacherVector {ι : Type*} [Fintype ι] :
    ∀ᵐ ξ ∂rademacherVector ι, ∀ i, ξ i ^ 2 = 1 := by
  rw [ae_all_iff]
  intro i
  filter_upwards [ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure
    (hasLaw_eval_rademacherVector i)] with ξ hξ
  rcases hξ with hξ | hξ <;> simp [hξ]

end NLAlib
