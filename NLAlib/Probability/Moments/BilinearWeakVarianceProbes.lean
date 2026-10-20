import NLAlib.Probability.Moments.BilinearWeakVariance
import NLAlib.Probability.Moments.BilinearSumCovariance
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Probability.HasLaw

/-! # Unit-sphere and independent-sum bilinear weak variance

The library's closed-unit-ball definition equals the source unit-sphere
supremum in nonzero dimension. Native independence and centering identify
the original increment probe budget with the weak variance of the actual
shifted sum law. Source: arXiv:2201.05142v3, Section 2.1 and Theorem 2.6.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => EuclideanSpace ℂ n

omit [DecidableEq n] in
private theorem norm_bilinear_real_smul (A : M) (v w : E) (a b : ℝ) :
    ‖star (a•v).ofLp ⬝ᵥ (A *ᵥ (b•w).ofLp)‖ =
      |a| * |b| * ‖star v.ofLp ⬝ᵥ (A *ᵥ w.ofLp)‖ := by
  simp only [WithLp.ofLp_smul,Matrix.mulVec_smul,star_smul,star_trivial,
    smul_dotProduct,dotProduct_smul,smul_smul,norm_smul,Real.norm_eq_abs,abs_mul]
  ring

open scoped Matrix.Norms.L2Operator in
private theorem unitBall_bilinear_budget_of_unitSphere
    (μ : Measure M) {b : ℝ} (hb : 0≤b)
    (h : ∀ v w : E, ‖v‖=1 → ‖w‖=1 →
      (∫ A : M, ‖star v.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w.ofLp)‖^2 ∂μ)≤b)
    (v w : E) (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    (∫ A : M, ‖star v.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w.ofLp)‖^2 ∂μ)≤b := by
  by_cases hv0 : v=0
  · simpa [hv0] using hb
  by_cases hw0 : w=0
  · simpa [hw0] using hb
  let v' := NormedSpace.normalize v
  let w' := NormedSpace.normalize w
  have hn : ‖v‖*‖w‖≤1 := by
    simpa only [one_mul] using mul_le_mul hv hw (norm_nonneg w) (show (0 : ℝ)≤1 by norm_num)
  have hscale : (‖v‖*‖w‖)^2≤1 := pow_le_one₀ (mul_nonneg (norm_nonneg v) (norm_nonneg w)) hn
  have he (A : M) :
      ‖star v.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w.ofLp)‖^2 =
        (‖v‖*‖w‖)^2 * ‖star v'.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w'.ofLp)‖^2 := by
    have hh := norm_bilinear_real_smul (A-∫ B : M, B ∂μ) v' w' ‖v‖ ‖w‖
    simp only [v',w',NormedSpace.norm_smul_normalize,abs_of_nonneg (norm_nonneg _)] at hh
    rw [hh]
    ring
  calc
    _ = (‖v‖*‖w‖)^2 *
        (∫ A : M, ‖star v'.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w'.ofLp)‖^2 ∂μ) := by
      simp_rw [he]
      exact integral_const_mul _ _
    _ ≤ ∫ A : M, ‖star v'.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w'.ofLp)‖^2 ∂μ :=
      mul_le_of_le_one_left (integral_nonneg fun _ => sq_nonneg _) hscale
    _ ≤ b := h v' w' (NormedSpace.norm_normalize hv0) (NormedSpace.norm_normalize hw0)

open scoped Matrix.Norms.L2Operator in
/-- The defined centered bilinear weak variance equals the literal source
unit-sphere supremum in nonempty dimension. Genuine vector normalization
proves the reverse inequality; no maximizing probe is assumed.
Source: arXiv:2201.05142v3, Section 2.1, sigma-star.
atlas: independent-sum-spectrum-universality (partial) -/
theorem bilinearWeakVariance_eq_sSup_unitSphere [Nonempty n]
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ) :
    bilinearWeakVariance μ = sSup ((fun q : E×E => ∫ A : M,
      ‖star q.1.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ q.2.ofLp)‖^2 ∂μ) ''
        {q | ‖q.1‖=1 ∧ ‖q.2‖=1}) := by
  let S := ((fun q : E×E => ∫ A : M,
    ‖star q.1.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ q.2.ofLp)‖^2 ∂μ) ''
      {q | ‖q.1‖=1 ∧ ‖q.2‖=1})
  have hSb : BddAbove S := (bddAbove_centered_bilinear_moments μ hμ).mono (by
    rintro _ ⟨q,hq,rfl⟩
    exact ⟨q,⟨hq.1.le,hq.2.le⟩,rfl⟩)
  have hSn : 0≤sSup S := by
    apply Real.sSup_nonneg
    rintro _ ⟨q,_,rfl⟩
    exact integral_nonneg fun _ => sq_nonneg _
  have hSne : S.Nonempty := by
    obtain ⟨v,hv⟩ := exists_norm_eq E (show (0 : ℝ)≤1 by norm_num)
    exact ⟨_,⟨(v,v),⟨hv,hv⟩,rfl⟩⟩
  apply le_antisymm
  · apply bilinearWeakVariance_le μ
    exact unitBall_bilinear_budget_of_unitSphere μ hSn
      (fun v w hv hw => le_csSup hSb ⟨(v,w),⟨hv,hw⟩,rfl⟩)
  · apply csSup_le hSne
    rintro _ ⟨q,hq,rfl⟩
    exact integral_norm_sq_centered_bilinear_le_bilinearWeakVariance μ hμ q.1 q.2 hq.1.le hq.2.le

open scoped Matrix.Norms.L2Operator in
/-- The source unit-sphere budget bounds the actual closed-ball weak
variance. Nonnegativity of the budget includes zero variance explicitly.
Source: arXiv:2201.05142v3, Section 2.1, sigma-star. -/
theorem bilinearWeakVariance_le_of_unitSphere (μ : Measure M) {b : ℝ} (hb : 0≤b)
    (h : ∀ v w : E, ‖v‖=1 → ‖w‖=1 →
      (∫ A : M, ‖star v.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w.ofLp)‖^2 ∂μ)≤b) :
    bilinearWeakVariance μ≤b :=
  bilinearWeakVariance_le μ (unitBall_bilinear_budget_of_unitSphere μ hb h)

open scoped Matrix.Norms.L2Operator in
/-- Taking the square root of the defined squared weak variance gives
exactly the source supremum of the root mean square centered bilinear
probes. Both directions follow from the actual least-upper-bound property;
the square root is not merely bounded by a replacement parameter.
Source: arXiv:2201.05142v3, Section 2.1, sigma-star.
atlas: independent-sum-spectrum-universality (partial) -/
theorem sqrt_bilinearWeakVariance_eq_sSup_unitSphere [Nonempty n]
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ) :
    Real.sqrt (bilinearWeakVariance μ) = sSup ((fun q : E×E => Real.sqrt (∫ A : M,
      ‖star q.1.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ q.2.ofLp)‖^2 ∂μ)) ''
        {q | ‖q.1‖=1 ∧ ‖q.2‖=1}) := by
  let S := ((fun q : E×E => Real.sqrt (∫ A : M,
    ‖star q.1.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ q.2.ofLp)‖^2 ∂μ)) ''
      {q | ‖q.1‖=1 ∧ ‖q.2‖=1})
  have hSne : S.Nonempty := by
    obtain ⟨v,hv⟩ := exists_norm_eq E (show (0 : ℝ)≤1 by norm_num)
    exact ⟨_,⟨(v,v),⟨hv,hv⟩,rfl⟩⟩
  have hLUB : IsLUB S (Real.sqrt (bilinearWeakVariance μ)) := by
    constructor
    · rintro _ ⟨q,hq,rfl⟩
      exact Real.sqrt_le_sqrt (integral_norm_sq_centered_bilinear_le_bilinearWeakVariance
        μ hμ q.1 q.2 hq.1.le hq.2.le)
    · intro b hb
      have hb0 : 0≤b := by
        obtain ⟨r,hr⟩ := hSne
        have hr0 : 0≤r := by
          rcases hr with ⟨q,_,rfl⟩
          exact Real.sqrt_nonneg _
        exact hr0.trans (hb hr)
      apply Real.sqrt_le_iff.mpr ⟨hb0,?_⟩
      apply bilinearWeakVariance_le_of_unitSphere μ (sq_nonneg b)
      intro v w hv hw
      exact (Real.sqrt_le_iff.mp (hb ⟨(v,w),⟨hv,hw⟩,rfl⟩)).2
  exact (hLUB.csSup_eq hSne).symm

open scoped Matrix.Norms.L2Operator in
/-- The literal marginal probe second moments of independent centered
increments are bounded by the centered bilinear weak variance of their
actual shifted sum law. All moments and the deterministic shift refer to
the original data; no covariance or budget certificate is assumed.
Source: arXiv:2201.05142v3, Section 2.1 and Theorem 2.6.
atlas: independent-sum-spectrum-universality (partial) -/
theorem sum_integral_norm_sq_bilinear_le_bilinearWeakVariance_shifted_sum
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → M) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω)≤R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i=0)
    (A₀ : M) (v w : E) (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    (∑ i, ∫ ω, ‖star v.ofLp ⬝ᵥ (Z i ω *ᵥ w.ofLp)‖^2 ∂ν i) ≤
      bilinearWeakVariance ((Measure.pi ν).map (fun x : ι → Ω => A₀+∑ i,Z i (x i))) := by
  classical
  let : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  let X (x : ι → Ω) := A₀+∑ i,Z i (x i)
  let ρ := (Measure.pi ν).map X
  have hXm : Measurable X := measurable_const.add (Finset.measurable_fun_sum _ fun i _ =>
    (hZm i).comp (measurable_pi_apply i))
  have hLaw : HasLaw X ρ (Measure.pi ν) := ⟨hXm.aemeasurable,rfl⟩
  let : IsProbabilityMeasure ρ := (Measure.pi ν).isProbabilityMeasure_map hXm.aemeasurable
  have hZi (i : ι) : MemLp (Z i) 2 (ν i) :=
    MemLp.of_bound (hZm i).aestronglyMeasurable R (hZ i)
  have hsum : MemLp (fun x : ι → Ω => ∑ i,Z i (x i)) 2 (Measure.pi ν) :=
    memLp_finsetSum Finset.univ fun i _ =>
      (hZi i).comp_measurePreserving (measurePreserving_eval ν i)
  have hX : MemLp X 2 (Measure.pi ν) := (memLp_const A₀).add hsum
  have hρ : MemLp (id : M → M) 2 ρ :=
    (memLp_map_measure_iff aestronglyMeasurable_id hXm.aemeasurable).mpr (by
      simpa only [Function.id_comp] using hX)
  have hsummean : (∫ x : ι → Ω, ∑ i,Z i (x i) ∂Measure.pi ν)=0 := by
    rw [integral_finsetSum Finset.univ (f := fun i (x : ι → Ω) => Z i (x i)) (fun i _ =>
      (measurePreserving_eval ν i).integrable_comp_of_integrable ((hZi i).integrable one_le_two))]
    simp only [integral_comp_eval (μ := ν) (i := _) (hZi _).aestronglyMeasurable,
      hmean,Finset.sum_const_zero]
  have hm : (∫ A : M,A ∂ρ)=A₀ := by
    rw [← hLaw.integral_eq]
    change (∫ x : ι → Ω,A₀+(∑ i,Z i (x i)) ∂Measure.pi ν)=A₀
    rw [integral_add (integrable_const A₀) (hsum.integrable one_le_two),
      integral_const,hsummean]
    simp
  have hc : Continuous (fun A : M =>
      ‖star v.ofLp ⬝ᵥ ((A-∫ B : M,B ∂ρ) *ᵥ w.ofLp)‖^2) := by fun_prop
  have he := hLaw.integral_comp hc.aestronglyMeasurable
  simp only [Function.comp_def,X,hm,add_sub_cancel_left] at he
  rw [← integral_norm_sq_bilinear_sum_pi_eq_sum ν Z hZm hZ hmean v w,he]
  simpa only [hm] using
    integral_norm_sq_centered_bilinear_le_bilinearWeakVariance ρ hρ v w hv hw

end NLAlib
