import NLAlib.Gaussian.Concentration.LipschitzConcentration
import NLAlib.Gaussian.LogSobolevCoverage
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Concentration from a genuine Euclidean logarithmic Sobolev inequality

The hypothesis is the usual Dirichlet-form inequality for arbitrary `C¹` test functions,
not an exponential-entropy assumption for the particular observable. Applying the inequality
to `exp(s f/2)` proves the exponential-entropy step of Herbst's argument.

Ledoux 2001, Theorems 5.1 and 5.3; atlas `herbst`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace NLAlib

/-- A probability measure satisfies the Euclidean logarithmic Sobolev inequality with
constant `c` if `Ent(g²)≤2c∫|∇g|²` for every `C¹` test function whose displayed integrals
are finite. The gradient is the standard coordinate Dirichlet form.
Ledoux 2001, Theorem 5.1; atlas `herbst` (general LSI premise). -/
structure HasEuclideanLogSobolev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (c : ℝ) : Prop where
  constant_nonneg : 0 ≤ c
  inequality : ∀ g : (ι → ℝ) → ℝ, ContDiff ℝ 1 g →
    Integrable (fun x => g x ^ 2) μ →
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ →
    Integrable (fun x => ∑ i, (fderiv ℝ g x (Pi.single i 1)) ^ 2) μ →
    (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂μ) -
      (∫ x, g x ^ 2 ∂μ) * Real.log (∫ x, g x ^ 2 ∂μ) ≤
        2 * c * ∫ x, ∑ i, (fderiv ℝ g x (Pi.single i 1)) ^ 2 ∂μ

private theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable f μ := by
  apply (integrable_const M).mono' hf.aestronglyMeasurable
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hM x

private theorem integrable_exp_mul_of_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (M : ℝ) (hM : ∀ x, |f x| ≤ M) (s : ℝ) :
    Integrable (fun x => Real.exp (s * f x)) μ := by
  apply (integrable_const (Real.exp (|s| * M))).mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  exact (le_abs_self (s * f x)).trans (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg s))

/-- A genuine LSI gives the exponential-entropy bound for a bounded smooth Lipschitz
observable, by the chain rule applied to `g=exp(s f/2)`. All three LSI integrability
requirements are proved from boundedness. Ledoux 2001, proof of Theorem 5.3;
atlas `herbst`. -/
theorem entropy_exp_mul_le_of_logSobolev_of_bounded
    {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] {c : ℝ} (hLSI : HasEuclideanLogSobolev μ c)
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) (s : ℝ) :
    (∫ x, s * f x * Real.exp (s * f x) ∂μ) -
      (∫ x, Real.exp (s * f x) ∂μ) * Real.log (∫ x, Real.exp (s * f x) ∂μ) ≤
        c * s ^ 2 * L ^ 2 / 2 * ∫ x, Real.exp (s * f x) ∂μ := by
  have hdiff := hf.differentiable one_ne_zero
  have hexp := integrable_exp_mul_of_abs_bound (μ := μ) hf.continuous.aemeasurable M hM s
  let G : (ι → ℝ) → ℝ := fun x => Real.exp (s / 2 * f x)
  have hGc : ContDiff ℝ 1 G := Real.contDiff_exp.comp (contDiff_const.mul hf)
  have hG2 : ∀ x, G x ^ 2 = Real.exp (s * f x) := by
    intro x
    dsimp [G]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hGd : ∀ x i, fderiv ℝ G x (Pi.single i 1) =
      Real.exp (s / 2 * f x) * (s / 2 * fderiv ℝ f x (Pi.single i 1)) := by
    intro x i
    have h := ((hdiff x).hasFDerivAt.const_mul (s / 2)).exp
    rw [h.fderiv]
    simp [smul_eq_mul]
  have hGd2 : ∀ x, ∑ i, (fderiv ℝ G x (Pi.single i 1)) ^ 2 =
      s ^ 2 / 4 * Real.exp (s * f x) * ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 := by
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hGd, ← hG2 x]
    dsimp [G]
    ring
  have hbd : ∀ x, ∑ i, (fderiv ℝ G x (Pi.single i 1)) ^ 2 ≤
      s ^ 2 * L ^ 2 / 4 * Real.exp (s * f x) := by
    intro x
    rw [hGd2]
    have h := sum_sq_fderiv_le_sq_of_lipschitz f hdiff L hLip x
    have h0 : 0 ≤ s ^ 2 / 4 * Real.exp (s * f x) := by positivity
    exact (mul_le_mul_of_nonneg_left h h0).trans_eq (by ring)
  have hdg_meas : AEStronglyMeasurable
      (fun x => ∑ i, (fderiv ℝ G x (Pi.single i 1)) ^ 2) μ := by
    refine Measurable.aestronglyMeasurable ?_
    apply Finset.measurable_sum
    intro i _
    exact (measurable_fderiv_apply_const ℝ G (Pi.single i 1)).pow_const 2
  have hdg : Integrable (fun x => ∑ i, (fderiv ℝ G x (Pi.single i 1)) ^ 2) μ := by
    apply (hexp.const_mul (s ^ 2 * L ^ 2 / 4)).mono' hdg_meas
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact hbd x
  have hg2 : Integrable (fun x => G x ^ 2) μ := by
    simp_rw [hG2]
    exact hexp
  have hglog : Integrable (fun x => G x ^ 2 * Real.log (G x ^ 2)) μ := by
    apply integrable_of_abs_bound
      (Real.continuous_mul_log.comp (hGc.continuous.pow 2)).aemeasurable
      (|s| * M * Real.exp (|s| * M))
    intro x
    change |G x ^ 2 * Real.log (G x ^ 2)| ≤ |s| * M * Real.exp (|s| * M)
    rw [hG2, Real.log_exp, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hsf : |s * f x| ≤ |s| * M := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg s)
    have hep : Real.exp (s * f x) ≤ Real.exp (|s| * M) :=
      Real.exp_le_exp.mpr ((le_abs_self _).trans hsf)
    simpa only [mul_comm] using
      mul_le_mul hep hsf (abs_nonneg (s * f x)) (Real.exp_pos _).le
  have key := hLSI.inequality G hGc hg2 hglog hdg
  have e1 : (fun x => G x ^ 2) = fun x => Real.exp (s * f x) := funext hG2
  have e2 : (fun x => G x ^ 2 * Real.log (G x ^ 2)) =
      fun x => s * f x * Real.exp (s * f x) := by
    funext x
    rw [hG2, Real.log_exp]
    ring
  rw [e1, e2] at key
  refine key.trans ?_
  calc
    2 * c * ∫ x, ∑ i, (fderiv ℝ G x (Pi.single i 1)) ^ 2 ∂μ ≤
        2 * c * ∫ x, s ^ 2 * L ^ 2 / 4 * Real.exp (s * f x) ∂μ :=
      mul_le_mul_of_nonneg_left (integral_mono hdg (hexp.const_mul _) hbd)
        (by positivity [hLSI.constant_nonneg])
    _ = _ := by rw [integral_const_mul]; ring

/-- A bounded smooth Lipschitz observable under a measure satisfying a genuine LSI has
the centered sub-Gaussian MGF with variance proxy `cL²`. Exponential integrability is
derived from boundedness. Ledoux 2001, Theorem 5.3; atlas `herbst`. -/
theorem hasSubgaussianMGF_of_logSobolev_of_bounded
    {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] {c : ℝ} (hLSI : HasEuclideanLogSobolev μ c)
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ)
      ⟨c * L ^ 2, mul_nonneg hLSI.constant_nonneg (sq_nonneg L)⟩ μ := by
  let E := ∫ y, f y ∂μ
  let C := c * L ^ 2 / 2
  have hint : ∀ s, Integrable (fun x => Real.exp (s * f x)) μ :=
    integrable_exp_mul_of_abs_bound hf.continuous.aemeasurable M hM
  have hent : ∀ s, (∫ x, s * f x * Real.exp (s * f x) ∂μ) -
      (∫ x, Real.exp (s * f x) ∂μ) * Real.log (∫ x, Real.exp (s * f x) ∂μ) ≤
        C * s ^ 2 * ∫ x, Real.exp (s * f x) ∂μ := by
    intro s
    have heq : c * s ^ 2 * L ^ 2 / 2 = C * s ^ 2 := by dsimp [C]; ring
    simpa only [heq] using
      entropy_exp_mul_le_of_logSobolev_of_bounded hLSI f hf L hLip M hM s
  have hraw : ∀ s, mgf f μ s ≤ Real.exp (s * E + C * s ^ 2) := by
    intro s
    by_cases hs : 0 ≤ s
    · exact integral_exp_mul_le_exp_of_entropy_le μ f C hint (fun s _ => hent s) s hs
    · have hintneg : ∀ u, Integrable (fun x => Real.exp (u * (-f x))) μ := by
        intro u
        simpa only [mul_neg, neg_mul] using hint (-u)
      have hentneg : ∀ u, 0 < u →
          (∫ x, u * (-f x) * Real.exp (u * (-f x)) ∂μ) -
            (∫ x, Real.exp (u * (-f x)) ∂μ) * Real.log (∫ x, Real.exp (u * (-f x)) ∂μ) ≤
              C * u ^ 2 * ∫ x, Real.exp (u * (-f x)) ∂μ := by
        intro u _
        simpa only [mul_neg, neg_mul, neg_sq] using hent (-u)
      have h := integral_exp_mul_le_exp_of_entropy_le μ (fun x => -f x) C
        hintneg hentneg (-s) (by linarith)
      simpa only [mgf, E, neg_mul, mul_neg, neg_neg, integral_neg, neg_sq] using h
  refine ⟨?_, ?_⟩
  · intro s
    have heq : (fun x => Real.exp (s * (f x - E))) =
        fun x => Real.exp (-(s * E)) * Real.exp (s * f x) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    change Integrable (fun x => Real.exp (s * (f x - E))) μ
    rw [heq]
    exact (hint s).const_mul _
  · intro s
    change mgf (fun x => f x - E) μ s ≤ Real.exp (c * L ^ 2 * s ^ 2 / 2)
    have heq : mgf (fun x => f x - E) μ s = Real.exp (-(s * E)) * mgf f μ s := by
      simp only [sub_eq_add_neg, mgf_add_const, mul_neg]
      ring
    rw [heq]
    calc
      Real.exp (-(s * E)) * mgf f μ s ≤
          Real.exp (-(s * E)) * Real.exp (s * E + C * s ^ 2) :=
        mul_le_mul_of_nonneg_left (hraw s) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        dsimp [C]
        ring

private def clipValue (a u : ℝ) : ℝ := max (-a) (min a u)

private theorem clipValue_abs_sub_le (a u v : ℝ) :
    |clipValue a u - clipValue a v| ≤ |u - v| := by
  have h1 := abs_max_sub_max_le_max (-a) (min a u) (-a) (min a v)
  have h2 := abs_min_sub_min_le_max a u a v
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min a u - min a v))] at h1
  rw [max_eq_right (abs_nonneg (u - v))] at h2
  exact h1.trans h2

private theorem clipValue_abs_le_bound {a : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    |clipValue a u| ≤ a := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private theorem clipValue_eq_of_abs_le {a u : ℝ} (hu : |u| ≤ a) : clipValue a u = u := by
  rcases abs_le.mp hu with ⟨hlo, hhi⟩
  rw [clipValue, min_eq_right hhi, max_eq_right hlo]

private theorem clipValue_abs_le {a : ℝ} (ha : 0 ≤ a) (u : ℝ) : |clipValue a u| ≤ |u| := by
  by_cases hhi : u ≤ a
  · by_cases hlo : -a ≤ u
    · rw [clipValue, min_eq_right hhi, max_eq_right hlo]
    · have hu0 : u ≤ 0 := by linarith
      rw [clipValue, min_eq_right hhi, max_eq_left (not_le.mp hlo).le,
        abs_neg, abs_of_nonneg ha, abs_of_nonpos hu0]
      linarith
  · have hu0 : 0 ≤ u := by linarith
    rw [clipValue, min_eq_left (not_le.mp hhi).le,
      max_eq_right (by linarith), abs_of_nonneg ha, abs_of_nonneg hu0]
    exact (not_le.mp hhi).le

/-- Every Euclidean Lipschitz function admits bounded smooth approximants preserving its
Lipschitz constant. They converge pointwise and satisfy `|fₙ|≤|f|+1`, so once `f` is
integrable the means converge by dominated convergence. Clamping is performed before
mollification. Ledoux 2001, proof of Theorem 5.3; atlas `herbst` (approximation helper). -/
theorem exists_bounded_contDiff_lipschitz_approx {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    ∃ F : ℕ → (ι → ℝ) → ℝ,
      (∀ n, ContDiff ℝ 1 (F n)) ∧
      (∀ n x y, |F n x - F n y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) ∧
      (∀ n x, |F n x| ≤ (n : ℝ) + 2) ∧
      (∀ n x, |F n x| ≤ |f x| + 1) ∧
      ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let H : ℕ → (ι → ℝ) → ℝ := fun n x => clipValue ((n : ℝ) + 1) (f x)
  have hH : ∀ n x y, |H n x - H n y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2) :=
    fun n x y => (clipValue_abs_sub_le _ _ _).trans (hLip x y)
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεle : ∀ n, ε n ≤ 1 := by
    intro n
    dsimp [ε]
    apply (div_le_one (by positivity)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hexists := fun n => exists_contDiff_abs_sub_le_of_lipschitz
    (H n) L (hH n) (ε n) (hεpos n)
  choose F hFc hFL hApprox using hexists
  refine ⟨F, fun n => hFc n 1, hFL, ?_, ?_, ?_⟩
  · intro n x
    have hclip := clipValue_abs_le_bound (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (f x)
    have htri := abs_sub_abs_le_abs_sub (F n x) (H n x)
    have hap := hApprox n x
    dsimp [H] at htri hap
    linarith [hεle n]
  · intro n x
    have hclip := clipValue_abs_le (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (f x)
    have htri := abs_sub_abs_le_abs_sub (F n x) (H n x)
    have hap := hApprox n x
    dsimp [H] at htri hap
    linarith [hεle n]
  · intro x
    obtain ⟨N, hN⟩ := exists_nat_ge |f x|
    have hap : ∀ᶠ n : ℕ in atTop, ‖F n x - f x‖ ≤ ε n := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hclip : H n x = f x := clipValue_eq_of_abs_le (by linarith)
      simpa only [Real.norm_eq_abs, hclip] using hApprox n x
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hap ?_
    simpa only [ε, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

private theorem lintegral_ofReal_le_of_tendsto_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {b : ℕ → ℝ} {B : ℝ}
    (hint : ∀ n, Integrable (F n) μ) (hpos : ∀ n x, 0 ≤ F n x)
    (hconv : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, ∫ x, F n x ∂μ ≤ b n) (hb : Tendsto b atTop (𝓝 B)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal B := by
  have hf := lintegral_liminf_le' (u := (atTop : Filter ℕ))
    (f := fun n x => ENNReal.ofReal (F n x))
    (fun n => (hint n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have heq : ∀ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop = ENNReal.ofReal (f x) :=
    fun x => (ENNReal.tendsto_ofReal (hconv x)).liminf_eq
  simp_rw [heq] at hf
  refine hf.trans ?_
  have hle := Filter.liminf_le_liminf (f := (atTop : Filter ℕ)) (Eventually.of_forall fun n =>
    show (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) ≤ ENNReal.ofReal (b n) from by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (hpos n))]
      exact ENNReal.ofReal_le_ofReal (hbound n))
  exact hle.trans_eq (ENNReal.tendsto_ofReal hb).liminf_eq

/-- The uncentered MGF estimate corresponding to the bounded smooth LSI theorem.
Ledoux 2001, Theorem 5.3; atlas `herbst` (bounded approximation endpoint). -/
theorem integral_exp_mul_le_of_logSobolev_of_bounded
    {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] {c : ℝ} (hLSI : HasEuclideanLogSobolev μ c)
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) (s : ℝ) :
    mgf f μ s ≤ Real.exp (s * (∫ y, f y ∂μ) + c * L ^ 2 * s ^ 2 / 2) := by
  let E := ∫ y, f y ∂μ
  have hSG := hasSubgaussianMGF_of_logSobolev_of_bounded hLSI f hf L hLip M hM
  have hbound := hSG.mgf_le s
  change mgf (fun x => f x - E) μ s ≤ Real.exp (c * L ^ 2 * s ^ 2 / 2) at hbound
  have hfun : (fun x => E + (f x - E)) = f := by funext x; ring
  have heq := mgf_const_add (X := fun x => f x - E) (μ := μ) (t := s) E
  rw [hfun] at heq
  rw [heq]
  calc
    Real.exp (s * E) * mgf (fun x => f x - E) μ s ≤
        Real.exp (s * E) * Real.exp (c * L ^ 2 * s ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

private theorem mean_bound_of_mass_and_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hexp : ∀ s : ℝ, Integrable (fun x => Real.exp (s * f x)) μ)
    (q : ℝ) (hraw : ∀ s : ℝ, mgf f μ s ≤ Real.exp (s * (∫ x, f x ∂μ) + q * s ^ 2))
    (A : Set Ω) (hA : MeasurableSet A) (hδ : 0 < μ.real A)
    (a : ℝ) (hOnA : ∀ x ∈ A, |f x| ≤ a) :
    |∫ x, f x ∂μ| ≤ a + q - Real.log (μ.real A) := by
  have hlow : ∀ s : ℝ, |s| ≤ 1 →
      μ.real A * Real.exp (-a) ≤ mgf f μ s := by
    intro s hs
    have hpoint : ∀ x, A.indicator (fun _ => Real.exp (-a)) x ≤ Real.exp (s * f x) := by
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        apply Real.exp_le_exp.mpr
        have habs : |s * f x| ≤ a := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans
            (by simpa only [one_mul] using hOnA x hx)
        exact (abs_le.mp habs).1
      · rw [Set.indicator_of_notMem hx]
        exact (Real.exp_pos _).le
    have hi := integral_mono ((integrable_const (Real.exp (-a))).indicator hA) (hexp s) hpoint
    simpa only [integral_indicator_const _ hA, smul_eq_mul, mgf] using hi
  have hlog (s : ℝ) (hs : |s| ≤ 1) :
      Real.log (μ.real A) - a ≤ s * (∫ x, f x ∂μ) + q * s ^ 2 := by
    have h := Real.log_le_log (mul_pos hδ (Real.exp_pos _)) ((hlow s hs).trans (hraw s))
    rw [Real.log_mul hδ.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at h
    linarith
  have hup := hlog (-1) (by norm_num)
  have hlo := hlog 1 (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith

private theorem abs_le_exp_add_exp_neg (u : ℝ) : |u| ≤ Real.exp u + Real.exp (-u) := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    linarith [Real.add_one_le_exp u, Real.exp_pos (-u)]
  · rw [abs_of_nonpos hu]
    linarith [Real.add_one_le_exp (-u), Real.exp_pos u]

/-- A genuine Euclidean LSI already forces integrability of every Lipschitz observable.
No moment or exponential-integrability hypothesis is assumed. Bounded approximants have
uniformly bounded means, using any positive-mass bounded-value event; Fatou then bounds
the first absolute moment. Ledoux 2001, proof of Theorem 5.3; atlas `herbst`. -/
theorem integrable_of_logSobolev_of_lipschitz
    {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] {c : ℝ} (hLSI : HasEuclideanLogSobolev μ c)
    (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    Integrable f μ := by
  have hfcont := continuous_of_abs_sub_le_mul_sqrt_sum_sq f L hL hLip
  obtain ⟨F, hFc, hFL, hFb, hDom, hConv⟩ := exists_bounded_contDiff_lipschitz_approx f L hLip
  let q := c * L ^ 2 / 2
  have hRaw : ∀ n s, mgf (F n) μ s ≤ Real.exp (s * (∫ x, F n x ∂μ) + q * s ^ 2) := by
    intro n s
    have heq : q * s ^ 2 = c * L ^ 2 * s ^ 2 / 2 := by dsimp [q]; ring
    simpa only [heq] using integral_exp_mul_le_of_logSobolev_of_bounded
      hLSI (F n) (hFc n) L (hFL n) ((n : ℝ) + 2) (hFb n) s
  have hInt : ∀ n, Integrable (F n) μ := fun n =>
    integrable_of_abs_bound (hFc n).continuous.aemeasurable ((n : ℝ) + 2) (hFb n)
  have hExp : ∀ n s, Integrable (fun x => Real.exp (s * F n x)) μ := fun n =>
    integrable_exp_mul_of_abs_bound (hFc n).continuous.aemeasurable ((n : ℝ) + 2) (hFb n)
  let A : ℕ → Set (ι → ℝ) := fun n => {x | |f x| ≤ (n : ℝ)}
  have hUnion : (⋃ n, A n) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact exists_nat_ge |f x|
  obtain ⟨a, ha⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (μ := μ) (s := A) (by rw [hUnion]; simp)
  have hA : MeasurableSet (A a) := measurableSet_le hfcont.abs.measurable measurable_const
  have hδ : 0 < μ.real (A a) := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  let U := (a : ℝ) + 1 + q - Real.log (μ.real (A a))
  have hMean : ∀ n, |∫ x, F n x ∂μ| ≤ U := by
    intro n
    apply mean_bound_of_mass_and_mgf (hExp n) q (hRaw n) (A a) hA hδ ((a : ℝ) + 1)
    intro x hx
    change |f x| ≤ (a : ℝ) at hx
    exact (hDom n x).trans (by linarith)
  have hAbsBound : ∀ n, ∫ x, |F n x| ∂μ ≤ 2 * Real.exp (U + q) := by
    intro n
    have hup : mgf (F n) μ 1 ≤ Real.exp (U + q) := by
      have h := hRaw n 1
      norm_num at h
      exact h.trans (Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hMean n)).2]))
    have hlo : mgf (F n) μ (-1) ≤ Real.exp (U + q) := by
      have h := hRaw n (-1)
      norm_num at h
      exact h.trans (Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hMean n)).1]))
    have hiP : Integrable (fun x => Real.exp (F n x)) μ := by simpa using hExp n 1
    have hiN : Integrable (fun x => Real.exp (-F n x)) μ := by simpa using hExp n (-1)
    calc
      ∫ x, |F n x| ∂μ ≤ ∫ x, Real.exp (F n x) + Real.exp (-F n x) ∂μ :=
        integral_mono (hInt n).abs (hiP.add hiN) (fun x => abs_le_exp_add_exp_neg _)
      _ = mgf (F n) μ 1 + mgf (F n) μ (-1) := by
        rw [integral_add hiP hiN]
        simp only [mgf, one_mul, neg_one_mul]
      _ ≤ _ := by linarith
  have hFatou := lintegral_ofReal_le_of_tendsto_integral_bound
    (F := fun n x => |F n x|) (f := fun x => |f x|)
    (b := fun _ => 2 * Real.exp (U + q)) (fun n => (hInt n).abs)
    (fun _ _ => abs_nonneg _) (fun x => (hConv x).abs) hAbsBound tendsto_const_nhds
  have hAbsInt : Integrable (fun x => |f x|) μ := ⟨hfcont.abs.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => abs_nonneg (f x)))).2
      (hFatou.trans_lt ENNReal.ofReal_lt_top)⟩
  exact hAbsInt.mono' hfcont.aestronglyMeasurable (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using (le_refl |f x|))

/-- **General LSI-to-Herbst concentration, with automatic integrability.** Under a genuine
Euclidean LSI with constant `c`, every `L`-Lipschitz real observable is integrable and its
centered MGF is sub-Gaussian with variance proxy `cL²`. No smoothness, finite-moment or
exponential-integrability assumption is imposed on the observable.
Ledoux 2001, Theorem 5.3; atlas `herbst`. -/
theorem integrable_and_hasSubgaussianMGF_of_logSobolev
    {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] {c : ℝ} (hLSI : HasEuclideanLogSobolev μ c)
    (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    Integrable f μ ∧ HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ)
      ⟨c * L ^ 2, mul_nonneg hLSI.constant_nonneg (sq_nonneg L)⟩ μ := by
  have hfInt := integrable_of_logSobolev_of_lipschitz hLSI f L hL hLip
  have hfcont := continuous_of_abs_sub_le_mul_sqrt_sum_sq f L hL hLip
  obtain ⟨F, hFc, hFL, hFb, hDom, hConv⟩ := exists_bounded_contDiff_lipschitz_approx f L hLip
  have hMeanConv : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |f x| + 1)
      (fun n => (hFc n).continuous.aestronglyMeasurable)
      (hfInt.abs.add (integrable_const (1 : ℝ)))
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ hConv)
    simpa only [Real.norm_eq_abs] using hDom n x
  have hRaw : ∀ s : ℝ, Integrable (fun x => Real.exp (s * f x)) μ ∧
      mgf f μ s ≤ Real.exp (s * (∫ x, f x ∂μ) + c * L ^ 2 * s ^ 2 / 2) := by
    intro s
    have hExp : ∀ n, Integrable (fun x => Real.exp (s * F n x)) μ := fun n =>
      integrable_exp_mul_of_abs_bound (hFc n).continuous.aemeasurable
        ((n : ℝ) + 2) (hFb n) s
    have hBound : ∀ n, (∫ x, Real.exp (s * F n x) ∂μ) ≤
        Real.exp (s * (∫ x, F n x ∂μ) + c * L ^ 2 * s ^ 2 / 2) :=
      fun n => integral_exp_mul_le_of_logSobolev_of_bounded hLSI (F n) (hFc n)
        L (hFL n) ((n : ℝ) + 2) (hFb n) s
    have hb : Tendsto (fun n => Real.exp (s * (∫ x, F n x ∂μ) + c * L ^ 2 * s ^ 2 / 2))
        atTop (𝓝 (Real.exp (s * (∫ x, f x ∂μ) + c * L ^ 2 * s ^ 2 / 2))) :=
      (Real.continuous_exp.tendsto _).comp
        (((tendsto_const_nhds (x := s)).mul hMeanConv).add tendsto_const_nhds)
    have hFatou := lintegral_ofReal_le_of_tendsto_integral_bound hExp
      (fun _ _ => (Real.exp_pos _).le)
      (fun x => (Real.continuous_exp.tendsto _).comp
        ((tendsto_const_nhds (x := s)).mul (hConv x))) hBound hb
    have hnonneg : 0 ≤ᵐ[μ] fun x => Real.exp (s * f x) :=
      ae_of_all _ fun _ => (Real.exp_pos _).le
    have hfi : Integrable (fun x => Real.exp (s * f x)) μ :=
      (lintegral_ofReal_ne_top_iff_integrable
        ((Real.continuous_exp.comp (continuous_const.mul hfcont)).aestronglyMeasurable)
        hnonneg).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFatou)
    refine ⟨hfi, ?_⟩
    apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp
    change ENNReal.ofReal (∫ x, Real.exp (s * f x) ∂μ) ≤ _
    rw [ofReal_integral_eq_lintegral_ofReal hfi hnonneg]
    exact hFatou
  refine ⟨hfInt, ?_⟩
  let E := ∫ y, f y ∂μ
  refine ⟨?_, ?_⟩
  · intro s
    have heq : (fun x => Real.exp (s * (f x - E))) =
        fun x => Real.exp (-(s * E)) * Real.exp (s * f x) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    change Integrable (fun x => Real.exp (s * (f x - E))) μ
    rw [heq]
    exact (hRaw s).1.const_mul _
  · intro s
    change mgf (fun x => f x - E) μ s ≤ Real.exp (c * L ^ 2 * s ^ 2 / 2)
    have heq : mgf (fun x => f x - E) μ s = Real.exp (-(s * E)) * mgf f μ s := by
      simp only [sub_eq_add_neg, mgf_add_const, mul_neg]
      ring
    rw [heq]
    calc
      Real.exp (-(s * E)) * mgf f μ s ≤
          Real.exp (-(s * E)) * Real.exp (s * E + c * L ^ 2 * s ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (hRaw s).2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- General LSI gives the one-sided Herbst concentration inequality
`P(f≥Ef+t)≤exp(-t²/(2cL²))` for every nonnegative threshold. Observable integrability
and all exponential moments are proved by the preceding theorem.
Ledoux 2001, Theorem 5.3; atlas `herbst`. -/
theorem measure_ge_le_of_logSobolev
    {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] {c : ℝ} (hLSI : HasEuclideanLogSobolev μ c)
    (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    μ {x | (∫ y, f y ∂μ) + t ≤ f x} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (c * L ^ 2)))) := by
  have hSG := (integrable_and_hasSubgaussianMGF_of_logSobolev hLSI f L hL hLip).2
  have htBound := hSG.measure_ge_le ht
  have hSet : {x | t ≤ f x - ∫ y, f y ∂μ} = {x | (∫ y, f y ∂μ) + t ≤ f x} := by
    ext x
    change (t ≤ f x - ∫ y, f y ∂μ) ↔ ((∫ y, f y ∂μ) + t ≤ f x)
    constructor <;> intro h <;> linarith
  rw [hSet] at htBound
  rw [← ofReal_measureReal (μ := μ)]
  exact ENNReal.ofReal_le_ofReal htBound

/-- The product standard Gaussian measure satisfies the genuine Euclidean LSI premise
with constant one. This bridge uses the already proved Dirichlet inequality; the generic
Herbst proof above does not use Gaussian exponential-integrability facts.
Gross 1975; Ledoux 2001, Theorem 5.1; atlas `gaussian-log-sobolev`, `herbst`. -/
theorem hasEuclideanLogSobolev_pi_gaussianReal {ι : Type*} [Fintype ι] [DecidableEq ι] :
    HasEuclideanLogSobolev (Measure.pi fun _ : ι => gaussianReal 0 1) 1 := by
  refine ⟨by norm_num, ?_⟩
  intro g hg hg2 hglog hdg
  simpa only [mul_one] using
    entropy_sq_le_two_mul_integral_sum_sq_fderiv_gaussian g hg hg2 hglog hdg

/-- A genuine Euclidean LSI forces entropy integrability whenever the square and
Dirichlet energy are integrable. Thus the finite-entropy testing convention in the
premise loses no `C¹` functions of finite energy. The proof uses bounded sine value
truncations and Fatou. Ledoux 2001, Theorem 5.1; atlas `gaussian-log-sobolev`, `herbst`. -/
theorem HasEuclideanLogSobolev.integrable_sq_mul_log_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] {c : ℝ} (hLSI : HasEuclideanLogSobolev μ c)
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hdf : Integrable (fun x => ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2) μ) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
  integrable_sq_mul_log_sq_of_logSobolev_bound (fun i : ι => Pi.single i (1 : ℝ))
    (2 * c) (mul_nonneg (by norm_num) hLSI.constant_nonneg) hLSI.inequality f hf hf2 hdf

/-- The Euclidean LSI inequality for every `C¹` function of finite square and Dirichlet
energy, with entropy integrability automatically discharged.
Ledoux 2001, Theorem 5.1; atlas `gaussian-log-sobolev`, `herbst`. -/
theorem HasEuclideanLogSobolev.inequality_of_integrable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] {c : ℝ} (hLSI : HasEuclideanLogSobolev μ c)
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hdf : Integrable (fun x => ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2) μ) :
    (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) -
      (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤
        2 * c * ∫ x, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ∂μ :=
  hLSI.inequality f hf hf2 (hLSI.integrable_sq_mul_log_sq f hf hf2 hdf) hdf

end NLAlib
