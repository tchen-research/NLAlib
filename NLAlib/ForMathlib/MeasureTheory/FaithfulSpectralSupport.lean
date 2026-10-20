import NLAlib.ForMathlib.MeasureTheory.CStarSpectralMeasure
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.MeasureTheory.Measure.Support

/-!
# Faithfulness gives full support of the actual spectral measure

The positive functional only needs to be faithful on a closed star algebra
containing the chosen self-adjoint element. Actual continuous functional
calculus remains in that algebra; a genuine continuous bump in any purported
null neighborhood would contradict faithfulness. No full-support or spectral
measure identification premise is supplied. Trivial algebras are included.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology ComplexOrder ContinuousFunctionalCalculus
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem spectralSupportRealCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus
attribute [local instance] spectralSupportRealCFC

/-- The actual spectrum measure has full support if its positive functional is faithful on a closed generated algebra containing the self-adjoint element. -/
theorem support_positiveSpectrumMeasure_eq_univ_of_faithful
    (φ : A →ₚ[ℂ] ℂ) (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (hfaithful : ∀ b : A, b∈S → φ (star b*b)=0 → b=0)
    {a : A} (ha : IsSelfAdjoint a) (haS : a∈S) :
    (positiveSpectrumMeasure φ ha).support=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  by_contra hpos
  have hU0 : positiveSpectrumMeasure φ ha U=0 := le_antisymm (not_lt.mp hpos) (by positivity)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  let f : C(spectrum ℝ a,ℝ) :=
    ⟨fun y => max 0 (ε-dist y x),continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))⟩
  have hzero : (fun y => f y*f y)=ᵐ[positiveSpectrumMeasure φ ha] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hU0] with y hy
    have hd : ε≤dist y x := le_of_not_gt (fun h => hy (hball h))
    have hf : f y=0 := max_eq_left (sub_nonpos.mpr hd)
    simp only [hf,mul_zero,Pi.zero_apply]
  have hInt : ∫ y, (f*f) y ∂positiveSpectrumMeasure φ ha=0 := by
    change (∫ y, f y*f y ∂positiveSpectrumMeasure φ ha)=0
    rw [integral_congr_ae hzero]
    simp only [Pi.zero_apply,integral_zero]
  have hre : (φ (cfcHom ha (f*f))).re=0 :=
    (integral_positiveSpectrumMeasure φ ha (f*f)).symm.trans hInt
  have hnonneg : 0≤cfcHom ha (f*f) := (cfcHom_nonneg_iff _).mpr (fun y => mul_self_nonneg (f y))
  have him := (Complex.nonneg_iff.mp (φ.map_nonneg hnonneg)).2
  have hz : φ (cfcHom ha (f*f))=0 := Complex.ext hre him.symm
  let Sᵣ : StarSubalgebra ℝ A :=
    { S.toSubalgebra.restrictScalars ℝ with star_mem' := S.star_mem' }
  have hle : StarAlgebra.elemental ℝ a≤Sᵣ := by
    unfold StarAlgebra.elemental
    apply StarSubalgebra.topologicalClosure_minimal
    · exact StarAlgebra.adjoin_le (Set.singleton_subset_iff.mpr haS)
    · exact hS
  have hmem : cfcHom ha f∈S := hle (cfcHom_mem_elemental ha f)
  have hstar : star (cfcHom ha f)=cfcHom ha f := by rw [← map_star]; simp
  have hsq : cfcHom ha (f*f)=star (cfcHom ha f)*cfcHom ha f := by rw [map_mul,hstar]
  rw [hsq] at hz
  have hcf := hfaithful (cfcHom ha f) hmem hz
  have hf : f=0 := (cfcHom_injective ha) (by simpa only [map_zero] using hcf)
  have hx := congrArg (fun g : C(spectrum ℝ a,ℝ) => g x) hf
  have hε0 : ε=0 := by
    simpa only [f,ContinuousMap.coe_mk,ContinuousMap.zero_apply,dist_self,sub_zero,max_eq_right hε.le] using hx
  exact (ne_of_gt hε) hε0
