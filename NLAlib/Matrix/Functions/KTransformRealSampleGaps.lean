import NLAlib.Matrix.Functions.KTransformBoundaryUnits
import NLAlib.Matrix.Functions.KTransformRealBoundary
import NLAlib.ForMathlib.Analysis.Matrix.PosDefConnectedContinuation

/-! # Genuine positive sample gaps throughout the lower trace gap

A single native stable scalar seed starts positivity. The analytic
Stieltjes continuation gives a continuous Hermitian family, while the
actual positive sample-defect measures force every denominator to be
invertible. Connectedness then gives strict positivity throughout the
whole component, with no sample-gap premise.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- The true nonlinear upper branch has an actual analytic real
Stieltjes continuation with strictly positive native sample gaps at
every point below its characterized trace law. Invertibility comes
from the constructed positive defect measures; positivity propagates
from a native stable seed along the genuine connected real component.
Source: Montanari--Saeed (2026), Theorem 3, real-gap converse.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_posDef_sample_gap_real_stieltjes_extension_matrixKTransform
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ) (hmass : μ.mass=1)
    (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ)) :
    ∃ G : ℂ → M,
      (∀ z : ℂ, 0<z.im → G z=α•F z) ∧
      (∀ x : ℝ, (G x).IsHermitian) ∧
      ∀ u : ℝ, (∀ t ∈ (μ : Measure ℝ).support, u<t) →
        AnalyticAt ℂ G (u : ℂ) ∧ (G u).PosDef ∧ (deriv G (u : ℂ)).PosDef ∧
          ∀ T ∈ ν.support, ((α⁻¹•G u)⁻¹+T.val).PosDef := by
  obtain ⟨G,hGN,hreal,hGu⟩ :=
    exists_global_posDef_real_stieltjes_extension_matrixKTransform ν hν α hα F hFa hF μ hμ
  have hne : (μ : Measure ℝ)≠0 := by
    intro hz
    have hm : μ.mass=0 := by
      apply ENNReal.coe_injective
      rw [FiniteMeasure.ennreal_mass,hz]
      simp
    rw [hmass] at hm
    exact one_ne_zero hm
  let a : ℝ := sInf (μ : Measure ℝ).support
  have ha : a∈(μ : Measure ℝ).support := hcompact.sInf_mem (Measure.nonempty_support hne)
  have hbelow (u : ℝ) : u<a ↔ ∀ t ∈ (μ : Measure ℝ).support, u<t := by
    constructor
    · intro hu t ht
      exact lt_of_lt_of_le hu (csInf_le hcompact.bddBelow ht)
    · intro hu
      exact hu a ha
  let X := Iio a
  let : PreconnectedSpace X := Subtype.preconnectedSpace (convex_Iio a).isPreconnected
  let S : X → M := fun x => α⁻¹•G (x.val : ℂ)
  have hSp (x : X) : (S x).PosDef :=
    ((hGu x.val ((hbelow x.val).mp x.property)).2.1).smul (inv_pos.mpr hα)
  have hSc : Continuous S := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hc : ContinuousAt (fun x : X => G (x.val : ℂ)) x :=
      ((hGu x.val ((hbelow x.val).mp x.property)).1).continuousAt.comp
        (f := fun x : X => (x.val : ℂ))
        ((Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt)
    exact hc.const_smul α⁻¹
  have hYc : Continuous (fun x : X => (S x)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hasFDerivAt_matrixInverse (S x) (hSp x).isUnit).continuousAt.comp hSc.continuousAt
  obtain ⟨u0,S0,hmargin,hS0,_hK0,hG0⟩ :=
    exists_matrixKTransform_stable_scalar_stieltjes_seed ν hν α hα F hF μ hμ G
      (fun u hu => (hGu u hu).1) hGN
  have hu0 : u0<a := by linarith [hmargin a ha]
  let x0 : X := ⟨u0,hu0⟩
  have hS0eq : S x0=S0 := by
    simp only [S,x0,hG0,smul_smul,inv_mul_cancel₀ hα.ne',one_smul]
  have hgap (T : selfAdjoint M) (hT : T∈ν.support) :
      ∀ x : X, ((S x)⁻¹+T.val).PosDef := by
    apply Matrix.posDef_everywhere_of_preconnected_isUnit
      (fun x : X => (S x)⁻¹+T.val) (hYc.add continuous_const)
    · intro x
      exact (hSp x).inv.isHermitian.add T.property
    · intro x
      exact isUnit_inverse_add_below_matrixKTransform_trace_support ν hν α hα F hFa hF μ hμ
        G x.val ((hbelow x.val).mp x.property) (hGu x.val ((hbelow x.val).mp x.property)).1
          hGN (hGu x.val ((hbelow x.val).mp x.property)).2.1 T hT
    · exact ⟨x0,by rw [hS0eq]; exact hS0.2.1 T hT⟩
  refine ⟨G,hGN,hreal,?_⟩
  intro u hu
  exact ⟨(hGu u hu).1,(hGu u hu).2.1,(hGu u hu).2.2,
    fun T hT => hgap T hT ⟨u,(hbelow u).mpr hu⟩⟩

end NLAlib
