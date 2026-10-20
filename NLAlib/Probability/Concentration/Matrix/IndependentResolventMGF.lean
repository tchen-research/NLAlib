import NLAlib.Probability.Concentration.Entropy.RandomProxySubgamma
import NLAlib.Probability.Concentration.Matrix.ResolventVarianceProxyMGF
import NLAlib.Matrix.Functions.ResolventGradient
import NLAlib.Matrix.Functions.ResolventMeasurability
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Actual two-sided resolvent moments under bounded matrix coordinate laws

The actual random gradient, increment bound and proxy exponential moment are
all derived. A scalar truncation only inside the proof retains the original
almost-everywhere Hermitian and norm assumptions. The literal proxy appears
in the final estimate; a bound on its expectation is a separate step.

Source: arXiv:2201.05142v3, Lemma 5.8 and Proposition 5.6, with the
coefficient-one entropy constants developed here. This is a concentration
prerequisite for independent-sum-spectrum-universality, whose full spectral
conclusion still requires further proofs.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped Matrix
namespace NLAlib
variable {ι n Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- Actual nonreal resolvent norms of independent bounded Hermitian matrix
coordinates have either centered exponential moment bounded by the computed
variance proxy. The mean matrix is unrestricted. Matrix bounds and Hermitian
support need only hold almost everywhere on their actual marginal laws. -/
private theorem integral_exp_sign_mul_centered_specNorm_resolvent_pi_le_of_pos
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hR : 0 < R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZB : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hdom : Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)) * s < 1)
    {e : ℝ} (he : e = 1 ∨ e = -1) :
    (∫ x : ι → Ω, Real.exp (s * (e *
      (specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) -
        ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν)))
      ∂Measure.pi ν) ≤
    Real.exp ((6 * ∫ q : (ι → Ω) × (ι → Ω),
      resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R |ζ.im|
        ∂((Measure.pi ν).prod (Measure.pi ν))) * s ^ 2 /
      (1 - Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)) * s)) := by
  let : SecondCountableTopology (Matrix n n ℂ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  let μ := Measure.pi ν
  let P := μ.prod μ
  let η := |ζ.im|
  let a := 16 * R ^ 2 / η ^ 4 + 64 * R ^ 4 / η ^ 6
  let b := 2 * R / η ^ 2
  let M := η⁻¹
  let X : (ι → Ω) → Matrix n n ℂ := fun x => A₀ + ∑ i, Z i (x i)
  let f : (ι → Ω) → ℝ := fun x => specNorm (resolvent (X x) ζ)
  let fc : (ι → Ω) → ℝ := fun x => min M (f x)
  let W : ((ι → Ω) × (ι → Ω)) → ℝ := fun q =>
    resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R η
  have hη : 0 < η := abs_pos.mpr hζ
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := inv_nonneg.mpr hη.le
  have hXm : Measurable X := by
    dsimp [X]
    fun_prop
  have hfm : Measurable f := by
    dsimp only [f]
    simpa only [specNorm_eq_norm, Function.comp_def] using ((measurable_matrix_resolvent ζ).comp hXm).norm
  have hfcm : Measurable fc := measurable_const.min hfm
  have hfcb (x : ι → Ω) : |fc x| ≤ M := by
    rw [abs_of_nonneg (le_min hM (specNorm_nonneg _))]
    exact min_le_left _ _
  have hgood : ∀ᵐ x ∂μ, ∀ i, (Z i (x i)).IsHermitian ∧ specNorm (Z i (x i)) ≤ R := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval ν i).quasiMeasurePreserving.ae ((hZH i).and (hZB i))
  have hXH (x : ι → Ω) (hx : ∀ i, (Z i (x i)).IsHermitian) : (X x).IsHermitian :=
    hA₀.add (isSelfAdjoint_sum _ (fun i _ => hx i))
  have hfe : fc =ᵐ[μ] f := hgood.mono fun x hx =>
    min_eq_right ((hXH x (fun i => (hx i).1)).specNorm_resolvent_le hζ)
  have hreplace (x : ι → Ω) (i : ι) (t : Ω) :
      X (Function.update x i t) = X x - (Z i (x i) - Z i t) := by
    have hfun : (fun j => Z j (Function.update x i t j)) =
        Function.update (fun j => Z j (x j)) i (Z i t) := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    have hbase := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => Z j (x j)) (Z i (x i))
    simp only [Function.update_eq_self] at hbase
    dsimp only [X]
    rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i), hbase]
    abel
  have hjoint : ∀ᵐ q ∂P,
      (∀ i, (Z i (q.1 i)).IsHermitian ∧ specNorm (Z i (q.1 i)) ≤ R) ∧
      (∀ i, (Z i (q.2 i)).IsHermitian ∧ specNorm (Z i (q.2 i)) ≤ R) := by
    exact ((measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hgood).and
      ((measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hgood)
  have hfirst : ∀ᵐ q ∂P, fc q.1 = f q.1 :=
    (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hfe
  have hupdated (i : ι) : ∀ᵐ q ∂P,
      fc (Function.update q.1 i (q.2 i)) = f (Function.update q.1 i (q.2 i)) := by
    have hp := (measurePreserving_fst (μ := μ) (ν := μ)).comp
      (measurePreserving_prod_pi_update_swap ν i)
    exact hp.quasiMeasurePreserving.ae hfe
  have hgrad : ∀ᵐ q ∂P,
      (∑ i, max (fc q.1 - fc (Function.update q.1 i (q.2 i))) 0 ^ 2) ≤ W q := by
    filter_upwards [hjoint, hfirst, ae_all_iff.mpr hupdated] with q hq hf hu
    simp_rw [hf, hu]
    have h := sum_posPart_sq_specNorm_resolvent_sub_le_resolventVarianceProxy
      (X q.1) (hXH q.1 (fun i => (hq.1 i).1))
      (fun i => Z i (q.1 i) - Z i (q.2 i))
      (fun i => (hq.1 i).1.sub (hq.2 i).1) hR.le
      (fun i => (specNorm_sub_le _ _).trans (by linarith [(hq.1 i).2, (hq.2 i).2])) ζ hζ
    simpa only [f, hreplace] using h
  have hdiff (i : ι) : ∀ᵐ q ∂P,
      |fc q.1 - fc (Function.update q.1 i (q.2 i))| ≤ b := by
    filter_upwards [hjoint, hfirst, hupdated i] with q hq hf hu
    rw [hf, hu]
    have hD := (hq.1 i).1.sub (hq.2 i).1
    have hH := hXH q.1 (fun j => (hq.1 j).1)
    have h := abs_specNorm_resolvent_sub_le (X q.1)
      (X q.1 - (Z i (q.1 i) - Z i (q.2 i))) hH (hH.sub hD) ζ hζ
    have hsub : X q.1 - (X q.1 - (Z i (q.1 i) - Z i (q.2 i))) =
        Z i (q.1 i) - Z i (q.2 i) := by abel
    rw [hsub] at h
    have hbD : specNorm (Z i (q.1 i) - Z i (q.2 i)) ≤ 2 * R :=
      (specNorm_sub_le _ _).trans (by linarith [(hq.1 i).2, (hq.2 i).2])
    have hl := h.trans (mul_le_mul_of_nonneg_left hbD (sq_nonneg _))
    simpa only [f, hreplace, b, η, div_eq_mul_inv, inv_pow, mul_comm, mul_left_comm, mul_assoc] using hl
  have hba : b ^ 2 ≤ a := by
    have hb2 : b ^ 2 = 4 * R ^ 2 / η ^ 4 := by dsimp [b]; ring
    rw [hb2]
    exact (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg R] : 4 * R ^ 2 ≤ 16 * R ^ 2)
      (by positivity : 0 ≤ η ^ 4)).trans (le_add_of_nonneg_right (by positivity))
  have hθdom : a * (2 * a)⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hp := integrable_and_log_integral_exp_resolventVarianceProxy_copy_le
    ν Z hZm hR.le hZB (inv_nonneg.mpr (by positivity : 0 ≤ 2 * a)) hθdom
  change Integrable W P ∧ Integrable (fun q => Real.exp ((2 * a)⁻¹ * W q)) P ∧
    Real.log (∫ q, Real.exp ((2 * a)⁻¹ * W q) ∂P) ≤
      (2 * a)⁻¹ * (∫ q, W q ∂P) / (1 - a * (2 * a)⁻¹) at hp
  have hfunexp : (fun q => Real.exp ((2 * a)⁻¹ * W q)) =
      (fun q => Real.exp (W q / (2 * a))) := by ext q; congr 1; ring
  rw [hfunexp] at hp
  have hlog : Real.log (∫ q, Real.exp (W q / (2 * a)) ∂P) ≤ (∫ q, W q ∂P) / a := by
    apply hp.2.2.trans_eq
    field_simp [ha.ne']
    ring
  have h := integral_exp_sign_mul_sub_integral_pi_le_of_random_proxy ν fc hfcm M hM hfcb
    W hp.1 hgrad ha hb hba hdiff hp.2.1 hlog hs hdom he
  have hmean : (∫ x, fc x ∂μ) = ∫ x, f x ∂μ := integral_congr_ae hfe
  change (∫ x, Real.exp (s * (e * (fc x - ∫ y, fc y ∂μ))) ∂μ) ≤ _ at h
  rw [hmean] at h
  have heq : (fun x => Real.exp (s * (e * (fc x - ∫ y, f y ∂μ)))) =ᵐ[μ]
      fun x => Real.exp (s * (e * (f x - ∫ y, f y ∂μ))) :=
    hfe.mono fun x hx => congrArg (fun z => Real.exp (s * (e * (z - ∫ y, f y ∂μ)))) hx
  rw [integral_congr_ae heq] at h
  exact h

open scoped Matrix.Norms.L2Operator in
/-- Actual centered moments in either sign for every nonnegative summand
bound, including zero radius and empty matrix or coordinate dimensions.
The proxy is computed from the actual original/copy differences. -/
theorem integral_exp_sign_mul_centered_specNorm_resolvent_pi_le
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hR : 0 ≤ R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZB : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hdom : Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)) * s < 1)
    {e : ℝ} (he : e = 1 ∨ e = -1) :
    (∫ x : ι → Ω, Real.exp (s * (e *
      (specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) -
        ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν)))
      ∂Measure.pi ν) ≤
    Real.exp ((6 * ∫ q : (ι → Ω) × (ι → Ω),
      resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R |ζ.im|
        ∂((Measure.pi ν).prod (Measure.pi ν))) * s ^ 2 /
      (1 - Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)) * s)) := by
  rcases hR.eq_or_lt with hzero | hpos
  · subst R
    let μ := Measure.pi ν
    let f : (ι → Ω) → ℝ := fun x => specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ)
    let c := specNorm (resolvent A₀ ζ)
    have hZ0 (i : ι) : ∀ᵐ ω ∂ν i, Z i ω = 0 := (hZB i).mono fun ω hω => by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [specNorm_eq_norm] using hω) (norm_nonneg _)
    have harray : ∀ᵐ x ∂μ, ∀ i, Z i (x i) = 0 := ae_all_iff.mpr fun i =>
      (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZ0 i)
    have hfe : f =ᵐ[μ] fun _ => c := harray.mono fun x hx => by simp [f, c, hx]
    have hmean : (∫ x, f x ∂μ) = c := by
      rw [integral_congr_ae hfe, integral_const, probReal_univ, one_smul]
    have hcenter : (fun x => Real.exp (s * (e * (f x - ∫ y, f y ∂μ)))) =ᵐ[μ] fun _ => 1 :=
      hfe.mono fun x hx => by simp only [hmean, hx, sub_self, mul_zero, Real.exp_zero]
    have hleft : (∫ x, Real.exp (s * (e * (f x - ∫ y, f y ∂μ))) ∂μ) = 1 := by
      rw [integral_congr_ae hcenter, integral_const, probReal_univ, one_smul]
    change (∫ x, Real.exp (s * (e * (f x - ∫ y, f y ∂μ))) ∂μ) ≤ _
    rw [hleft]
    simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul,
      zero_div, add_zero, Real.sqrt_zero, sub_zero, div_one]
    have hW0 : 0 ≤ ∫ q : (ι → Ω) × (ι → Ω),
        resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ 0 |ζ.im|
          ∂((Measure.pi ν).prod (Measure.pi ν)) :=
      integral_nonneg fun _ => matrixVarianceProxy_nonneg _ _ (by positivity) (by positivity)
    exact Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hW0) (sq_nonneg s))
  · exact integral_exp_sign_mul_centered_specNorm_resolvent_pi_le_of_pos
      ν A₀ hA₀ Z hZm hpos hZH hZB ζ hζ hs hdom he

end NLAlib
