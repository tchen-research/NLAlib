import NLAlib.Matrix.Norms.MatrixVarianceProxy
import NLAlib.Probability.Concentration.Entropy.SelfBoundingMGF
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Actual self-bounding exponential moments of the resolvent variance proxy

The source-scaled matrix proxy has its deletion bound and coordinate
independence derived from its definition. Clipping only inside the proof
retains almost-everywhere marginal bounds and transports the result to the
actual original/copy joint law, with all displayed integrability derived.

These are concentration prerequisites for independent-sum-spectrum-universality;
the full spectral theorem remains separate. Source: arXiv:2201.05142v3,
Proposition 5.6 and Lemma 5.9, with coefficient-one entropy constants.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped Matrix
namespace NLAlib
variable {ι n : Type*} [Fintype n] [DecidableEq n]

section Probability
variable [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]

/-- Actual bounded matrix coordinate laws give the full self-bounding
log-MGF estimate. The self-bound and coordinate deletion independence are
derived here, and zero coefficient, empty family and empty dimension are retained. -/
theorem log_integral_exp_resolventVarianceProxy_pi_le_of_bounded
    (D : ι → Ω → Matrix n n ℂ) (hDm : ∀ i, Measurable (D i))
    {R η : ℝ} (hR : 0 ≤ R) (hD : ∀ i ω, specNorm (D i ω) ≤ 2 * R)
    {s : ℝ} (hs : 0 ≤ s)
    (hdom : (16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6) * s < 1) :
    Real.log (∫ x : ι → Ω,
      Real.exp (s * resolventVarianceProxy (fun i => D i (x i)) Finset.univ R η)
        ∂Measure.pi ν) ≤
      s * (∫ x : ι → Ω, resolventVarianceProxy (fun i => D i (x i)) Finset.univ R η
        ∂Measure.pi ν) / (1 - (16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6) * s) := by
  let α := 2 / η ^ 4
  let β := 8 * R ^ 2 / η ^ 6
  let W : (ι → Ω) → ℝ := fun x => resolventVarianceProxy (fun i => D i (x i)) Finset.univ R η
  let Wi : ι → (ι → Ω) → ℝ := fun i x =>
    resolventVarianceProxy (fun j => D j (x j)) (Finset.univ.erase i) R η
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hWm : Measurable W :=
    (measurable_matrixVarianceProxy Finset.univ α β).comp
      (measurable_pi_lambda _ fun i => (hDm i).comp (measurable_pi_apply i))
  have hW0 (x : ι → Ω) : 0 ≤ W x :=
    matrixVarianceProxy_nonneg _ _ hα hβ
  have hWb (x : ι → Ω) : |W x| ≤ (α + β) * (Fintype.card ι : ℝ) * (4 * R ^ 2) := by
    rw [abs_of_nonneg (hW0 x)]
    exact matrixVarianceProxy_le_card_mul _ hR hα hβ (fun i => hD i (x i))
  have hlower (i : ι) (x : ι → Ω) : Wi i x ≤ W x :=
    matrixVarianceProxy_mono _ (Finset.erase_subset _ _) hα hβ
  have hindep (i : ι) (x : ι → Ω) (t : Ω) : Wi i (Function.update x i t) = Wi i x := by
    apply matrixVarianceProxy_congr
    intro j hj
    simp only [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have hsum (x : ι → Ω) : ∑ i, (W x - Wi i x) ^ 2 ≤
      (16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6) * W x :=
    sum_sq_sub_resolventVarianceProxy_erase_le _ hR (fun i => hD i (x i))
  exact log_integral_exp_mul_pi_le_of_bounded_deletions ν W hWm _ (by positivity)
    hWb Wi hlower hindep (by positivity) hsum hs hdom


open scoped Matrix.Norms.L2Operator in
/-- The actual matrix coordinate laws satisfy exponential integrability and
the self-bounding log-MGF bound from almost-everywhere matrix bounds alone.
Clipping is used only inside the proof and is transported back to the
original matrix family. Neither independence of a random proxy nor a desired
exponential-moment comparison is assumed. -/
theorem integrable_and_log_integral_exp_resolventVarianceProxy_pi_le
    (D : ι → Ω → Matrix n n ℂ) (hDm : ∀ i, Measurable (D i))
    {R η : ℝ} (hR : 0 ≤ R)
    (hD : ∀ i, ∀ᵐ ω ∂ν i, specNorm (D i ω) ≤ 2 * R)
    {s : ℝ} (hs : 0 ≤ s)
    (hdom : (16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6) * s < 1) :
    Integrable (fun x : ι → Ω =>
      resolventVarianceProxy (fun i => D i (x i)) Finset.univ R η) (Measure.pi ν) ∧
    Integrable (fun x : ι → Ω =>
      Real.exp (s * resolventVarianceProxy (fun i => D i (x i)) Finset.univ R η)) (Measure.pi ν) ∧
    Real.log (∫ x : ι → Ω,
      Real.exp (s * resolventVarianceProxy (fun i => D i (x i)) Finset.univ R η)
        ∂Measure.pi ν) ≤
      s * (∫ x : ι → Ω, resolventVarianceProxy (fun i => D i (x i)) Finset.univ R η
        ∂Measure.pi ν) / (1 - (16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6) * s) := by
  classical
  let Dc : ι → Ω → Matrix n n ℂ := fun i ω =>
    if specNorm (D i ω) ≤ 2 * R then D i ω else 0
  have hDcm (i : ι) : Measurable (Dc i) := by
    apply Measurable.ite (measurableSet_le ?_ measurable_const) (hDm i) measurable_const
    simpa only [specNorm_eq_norm] using (hDm i).norm
  have hDcb (i : ι) (ω : Ω) : specNorm (Dc i ω) ≤ 2 * R := by
    dsimp only [Dc]
    split_ifs with h
    · exact h
    · simpa only [specNorm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR
  have hDce (i : ι) : ∀ᵐ ω ∂ν i, Dc i ω = D i ω :=
    (hD i).mono fun ω hω => if_pos hω
  have harray : ∀ᵐ x ∂Measure.pi ν, (fun i => Dc i (x i)) = fun i => D i (x i) := by
    filter_upwards [ae_all_iff.mpr (fun i =>
      (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hDce i))] with x hx
    exact funext hx
  let W : (ι → Ω) → ℝ := fun x => resolventVarianceProxy (fun i => D i (x i)) Finset.univ R η
  let Wc : (ι → Ω) → ℝ := fun x => resolventVarianceProxy (fun i => Dc i (x i)) Finset.univ R η
  have hWe : Wc =ᵐ[Measure.pi ν] W := harray.mono fun x hx => congrArg
    (fun E => resolventVarianceProxy E Finset.univ R η) hx
  let α := 2 / η ^ 4
  let β := 8 * R ^ 2 / η ^ 6
  let M := (α + β) * (Fintype.card ι : ℝ) * (4 * R ^ 2)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hWcm : Measurable Wc :=
    (measurable_matrixVarianceProxy Finset.univ α β).comp
      (measurable_pi_lambda _ fun i => (hDcm i).comp (measurable_pi_apply i))
  have hWcb (x : ι → Ω) : |Wc x| ≤ M := by
    change |matrixVarianceProxy (fun i => Dc i (x i)) Finset.univ α β| ≤ M
    rw [abs_of_nonneg (matrixVarianceProxy_nonneg _ _ hα hβ)]
    exact matrixVarianceProxy_le_card_mul _ hR hα hβ (fun i => hDcb i (x i))
  have hWci : Integrable Wc (Measure.pi ν) := Integrable.of_bound
    hWcm.aestronglyMeasurable M (ae_of_all _ fun x => by simpa using hWcb x)
  have hWcexp : Integrable (fun x => Real.exp (s * Wc x)) (Measure.pi ν) := by
    apply Integrable.of_bound (by fun_prop) (Real.exp (|s| * M))
    exact ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        Real.exp_mul_le_exp_abs_mul_of_abs_le (s := s) (hWcb x)
  have hE : (fun x => Real.exp (s * Wc x)) =ᵐ[Measure.pi ν]
      fun x => Real.exp (s * W x) := hWe.mono fun x hx => congrArg (fun w : ℝ => Real.exp (s * w)) hx
  refine ⟨hWci.congr hWe, hWcexp.congr hE, ?_⟩
  have h := log_integral_exp_resolventVarianceProxy_pi_le_of_bounded ν Dc hDcm hR hDcb hs hdom
  change Real.log (∫ x, Real.exp (s * Wc x) ∂Measure.pi ν) ≤
    s * (∫ x, Wc x ∂Measure.pi ν) / _ at h
  rw [integral_congr_ae hE, integral_congr_ae hWe] at h
  exact h


open scoped Matrix.Norms.L2Operator in
/-- Actual independent-copy matrix differences satisfy the self-bounding
exponential estimate on the original/copy joint law. All matrix bounds may
hold only almost everywhere, and coordinate distributions may differ. -/
theorem integrable_and_log_integral_exp_resolventVarianceProxy_copy_le
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R η : ℝ} (hR : 0 ≤ R)
    (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    {s : ℝ} (hs : 0 ≤ s)
    (hdom : (16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6) * s < 1) :
    Integrable (fun q : (ι → Ω) × (ι → Ω) =>
      resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R η)
        ((Measure.pi ν).prod (Measure.pi ν)) ∧
    Integrable (fun q : (ι → Ω) × (ι → Ω) =>
      Real.exp (s * resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R η))
        ((Measure.pi ν).prod (Measure.pi ν)) ∧
    Real.log (∫ q : (ι → Ω) × (ι → Ω),
      Real.exp (s * resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R η)
        ∂((Measure.pi ν).prod (Measure.pi ν))) ≤
      s * (∫ q : (ι → Ω) × (ι → Ω),
        resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R η
          ∂((Measure.pi ν).prod (Measure.pi ν))) /
        (1 - (16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6) * s) := by
  let : SecondCountableTopology (Matrix n n ℂ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  let D : ι → Ω × Ω → Matrix n n ℂ := fun i p => Z i p.1 - Z i p.2
  have hDm (i : ι) : Measurable (D i) :=
    ((hZm i).comp measurable_fst).sub ((hZm i).comp measurable_snd)
  have hDb (i : ι) : ∀ᵐ p ∂(ν i).prod (ν i), specNorm (D i p) ≤ 2 * R := by
    filter_upwards [(measurePreserving_fst (μ := ν i) (ν := ν i)).quasiMeasurePreserving.ae (hZ i),
      (measurePreserving_snd (μ := ν i) (ν := ν i)).quasiMeasurePreserving.ae (hZ i)] with p h1 h2
    exact (specNorm_sub_le _ _).trans (by linarith)
  have h := integrable_and_log_integral_exp_resolventVarianceProxy_pi_le
    (fun i => (ν i).prod (ν i)) D hDm hR hDb hs hdom
  let F : ((ι → Ω) × (ι → Ω)) → ℝ := fun q =>
    resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R η
  have hFm : Measurable F :=
    (measurable_matrixVarianceProxy Finset.univ (2 / η ^ 4) (8 * R ^ 2 / η ^ 6)).comp
      (measurable_pi_lambda _ fun i =>
        ((hZm i).comp ((measurable_pi_apply i).comp measurable_fst)).sub
          ((hZm i).comp ((measurable_pi_apply i).comp measurable_snd)))
  have hp := measurePreserving_arrowProdEquivProdArrow Ω Ω ι ν ν
  have hFexp : Measurable (fun q => Real.exp (s * F q)) := (measurable_const.mul hFm).exp
  have hi : Integrable F ((Measure.pi ν).prod (Measure.pi ν)) :=
    (hp.integrable_comp hFm.aestronglyMeasurable).mp h.1
  have hiexp : Integrable (fun q => Real.exp (s * F q)) ((Measure.pi ν).prod (Measure.pi ν)) :=
    (hp.integrable_comp hFexp.aestronglyMeasurable).mp h.2.1
  refine ⟨hi, hiexp, ?_⟩
  have he := hp.hasLaw.integral_comp hFm.aestronglyMeasurable
  have hexp := hp.hasLaw.integral_comp hFexp.aestronglyMeasurable
  simp only [Function.comp_def] at he hexp
  have hlog := h.2.2
  change Real.log (∫ x, Real.exp (s * F ((MeasurableEquiv.arrowProdEquivProdArrow Ω Ω ι) x))
      ∂Measure.pi fun i => (ν i).prod (ν i)) ≤
    s * (∫ x, F ((MeasurableEquiv.arrowProdEquivProdArrow Ω Ω ι) x)
      ∂Measure.pi fun i => (ν i).prod (ν i)) / _ at hlog
  rw [hexp, he] at hlog
  exact hlog

end Probability
end NLAlib
