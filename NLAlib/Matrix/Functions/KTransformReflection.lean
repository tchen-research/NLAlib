import NLAlib.ForMathlib.MeasureTheory.MeasureSupportHomeomorph
import NLAlib.Matrix.Functions.KTransformAdjoint
import NLAlib.Matrix.Functions.KTransformUpperExistence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import NLAlib.Matrix.Basic.NormalizedTrace

/-! # Native reflection of the matrix K-transform

Negating the actual Hermitian sample law and its matrix argument
negates the true K-transform. The map integral uses an actual
measurable equivalence; no stochastic reflection identity is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- Negating the true sample law and matrix input negates the native
nonlinear K-transform. Only the actually used matrix inverse must be
a unit; the Bochner change of variables is a genuine measurable
negation equivalence.
Source: Montanari--Saeed (2026), Remark 3.1, reflected upper edge.
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_map_neg_neg
    (ν : Measure (selfAdjoint M)) (α : ℝ) (S : M) (hS : IsUnit S) :
    matrixKTransform (ν.map (fun T : selfAdjoint M => -T)) α (-S)=
      -matrixKTransform ν α S := by
  have hInv : (-S)⁻¹= -S⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [neg_mul_neg,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)]
  have hmap : (∫ T : selfAdjoint M,matrixKResolvent (-S) T.val
      ∂ν.map (fun T : selfAdjoint M => -T))=
      ∫ T : selfAdjoint M,matrixKResolvent (-S) (-T).val ∂ν := by
    exact integral_map_equiv (Homeomorph.neg (selfAdjoint M)).toMeasurableEquiv _
  have hker (T : selfAdjoint M) : matrixKResolvent (-S) (-T).val= -matrixKResolvent S T.val := by
    simp only [matrixKResolvent,AddSubgroup.coe_neg,neg_mul_neg,Matrix.neg_mul]
  simp only [matrixKTransform,hmap,hker,integral_neg,hInv,smul_neg]
  abel

private theorem imaginaryPart_neg_conjTranspose (A : M) :
    (imaginaryPart (-Aᴴ) : M)=(imaginaryPart A : M) := by
  simp only [imaginaryPart_apply_coe,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_neg,Matrix.conjTranspose_conjTranspose]
  congr 1
  abel

omit [DecidableEq n] in
private theorem normalizedTrace_real_smul_neg_conjTranspose (α : ℝ) (A : M) :
    normalizedTrace (α•(-Aᴴ))= -star (normalizedTrace (α•A)) := by
  simp [normalizedTrace,Matrix.trace_smul,Matrix.trace_conjTranspose]

variable [Nonempty n]

/-- The original sample negation constructs a genuine analytic native
K branch whose actual trace law is the reflection of the original law.
The branch reflection follows from the proved nonlinear uniqueness;
neither a reflection law nor a new matrix solution is assumed.
Source: Montanari--Saeed (2026), Remark 3.1, reflected upper edge.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_reflected_stieltjes_branch
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ)) :
    ∃ H : ℂ → M, AnalyticOnNhd ℂ H {z : ℂ | 0<z.im} ∧
      (∀ z : ℂ, 0<z.im → (imaginaryPart (H z) : M).PosDef ∧
        matrixKTransform (ν.map (fun T : selfAdjoint M => -T)) α (H z)=z•1) ∧
      (∀ z : ℂ, 0<z.im → H z= -(F (-star z))ᴴ) ∧
      ∀ z : ℂ, 0<z.im → normalizedTrace (α•H z)=
        ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ.map (fun t : ℝ => -t) : Measure ℝ) := by
  let η : Measure (selfAdjoint M) := ν.map (fun T : selfAdjoint M => -T)
  have hηc : IsCompact η.support := by
    have hs := Measure.support_map_homeomorph ν (Homeomorph.neg (selfAdjoint M))
    change η.support=(fun T : selfAdjoint M => -T) '' ν.support at hs
    rw [hs]
    exact hν.image continuous_neg
  have : IsProbabilityMeasure η := ν.isProbabilityMeasure_map continuous_neg.measurable.aemeasurable
  obtain ⟨H,hHa,hH0⟩ := exists_analytic_matrixKTransform_upperHalfPlane_solution η hηc α hα
  have hH (z : ℂ) (hz : 0<z.im) : (imaginaryPart (H z) : M).PosDef ∧
      matrixKTransform η α (H z)=z•1 := ⟨(hH0 z hz).1,(hH0 z hz).2.1⟩
  have heq (z : ℂ) (hz : 0<z.im) : H z= -(F (-star z))ᴴ := by
    let w : ℂ := -star z
    have hw : 0<w.im := by simpa [w,Complex.star_def] using hz
    have hFdom := mem_matrixKTransformDomain_of_posDef_imaginaryPart ν (hF w hw).1
    have hFstar : IsUnit (F w)ᴴ := by
      simpa only [Matrix.star_eq_conjTranspose] using hFdom.1.star
    have hcandidate : (imaginaryPart (-(F w)ᴴ) : M).PosDef := by
      rw [imaginaryPart_neg_conjTranspose]
      exact (hF w hw).1
    have hK : matrixKTransform η α (-(F w)ᴴ)=z•1 := by
      change matrixKTransform (ν.map (fun T : selfAdjoint M => -T)) α (-(F w)ᴴ)=z•1
      rw [matrixKTransform_map_neg_neg ν α _ hFstar,
        matrixKTransform_conjTranspose ν α (F w) hFdom,(hF w hw).2]
      simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_one,w]
      simp [neg_smul]
    have hZ : (imaginaryPart (z•(1 : M)) : M).PosDef := by
      have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
      have he : (imaginaryPart (z•(1 : M)) : M)=z.im•1 := by
        simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one]
      rw [he]
      exact Matrix.PosDef.one.smul hz
    exact matrixKTransform_solution_unique_upperHalfPlane η hηc α hα
      (z•1) (H z) (-(F w)ᴴ) hZ (hH z hz).1 hcandidate (hH z hz).2 hK
  refine ⟨H,hHa,hH,heq,?_⟩
  intro z hz
  let w : ℂ := -star z
  have hw : 0<w.im := by simpa [w,Complex.star_def] using hz
  rw [heq z hz,normalizedTrace_real_smul_neg_conjTranspose,hμ w hw]
  have hmap : (∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ.map (fun t : ℝ => -t) : Measure ℝ))=
      ∫ t : ℝ, (((-t : ℝ) : ℂ)-z)⁻¹ ∂(μ : Measure ℝ) :=
    integral_map_equiv (Homeomorph.neg ℝ).toMeasurableEquiv _
  rw [hmap,Complex.star_def,← integral_conj,← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    simp only [Complex.star_def,map_inv₀,map_sub,Complex.conj_ofReal,w,
      map_neg,Complex.conj_conj,Complex.ofReal_neg]
    rw [← inv_neg]
    congr 1
    ring

end NLAlib
