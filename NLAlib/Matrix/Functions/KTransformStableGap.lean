import NLAlib.Matrix.Functions.KTransformRealBranch
import NLAlib.Matrix.Functions.KTransformHalfPlaneUniqueness
import NLAlib.Matrix.Functions.KTransformUpperBounds
import NLAlib.Matrix.Norms.TraceImaginary
import NLAlib.ForMathlib.Analysis.Matrix.UpperHalfPlaneGerm
import NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesSupport

/-! # Stable scalar K solutions exclude genuine spectral support

The actual stable local inverse has positive imaginary part near the
real point. Native upper-half-plane uniqueness identifies it with the
constructed Stieltjes branch, and the proved height bound excludes the
real point from the representing measure's support.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter Set Metric
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

omit [Nonempty n] in
private theorem stableGap_scalar_im (z : ℂ) :
    (imaginaryPart (z•(1 : M)) : M)=z.im•1 := by
  have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
  simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one]

/-- The genuine local inverse at a stable real scalar K point agrees
with the actual upper-half-plane branch, and its imaginary part is
bounded by height. Local positivity is proved from the actual positive
derivative and native reflection, rather than assumed.
Source: Montanari--Saeed (2026), Theorem 3, branch identification.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_stable_branch_agrees_upper
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (S : M) (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hpos : ∀ H : M, H.IsHermitian → H≠0 →
      0<frobInner H (matrixKTransformDeriv ν α S H))
    (u : ℝ) (hK : matrixKTransform ν α S=(u : ℂ)•1) :
    ∃ (G : ℂ → M) (C : ℝ), AnalyticAt ℂ G (u : ℂ) ∧ G u=S ∧
      ∀ᶠ z : ℂ in 𝓝 (u : ℂ), 0<z.im → G z=F z ∧
        ‖(imaginaryPart (α•F z) : M)‖≤C*z.im := by
  obtain ⟨G,B,hGa,hG0,hB,hGd,hreal,hGeq⟩ :=
    exists_analytic_real_matrixKTransform_inverse_branch ν hν α hα S hS hgap hpos u hK
  obtain ⟨C,hupper⟩ := Matrix.eventually_posDef_imaginaryPart_of_posDef_deriv
    G u B hGa hGd hB hreal
  refine ⟨G,α*C,hGa,hG0,?_⟩
  filter_upwards [hupper,hGeq] with z hzG hzK
  intro hz
  have hZ : (imaginaryPart (z•(1 : M)) : M).PosDef := by
    rw [stableGap_scalar_im]
    exact Matrix.PosDef.one.smul hz
  have he := matrixKTransform_solution_unique_upperHalfPlane ν hν α hα
    (z•1) (G z) (F z) hZ (hzG hz).1 (hF z hz).1 hzK.2 (hF z hz).2
  refine ⟨he,?_⟩
  have hscale : (imaginaryPart (α•F z) : M)=α•(imaginaryPart (F z) : M) := by
    rw [map_smul]; rfl
  rw [hscale,norm_smul,Real.norm_of_nonneg hα.le,← he]
  exact (mul_le_mul_of_nonneg_left (hzG hz).2 hα.le).trans_eq (mul_assoc α C z.im).symm

/-- Every actual stable scalar K solution lies outside the support of
the genuine characterized Stieltjes law. Analytic continuation, local
imaginary positivity, and the support exclusion estimate are proved
from the native nonlinear equation.
Source: Montanari--Saeed (2026), Theorem 3, stable branch/support bridge.
atlas: block-wishart-variational-edges (partial) -/
theorem notMem_support_of_matrixKTransform_stable_solution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ))
    (S : M) (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hpos : ∀ H : M, H.IsHermitian → H≠0 →
      0<frobInner H (matrixKTransformDeriv ν α S H))
    (u : ℝ) (hK : matrixKTransform ν α S=(u : ℂ)•1) :
    u∉(μ : Measure ℝ).support := by
  obtain ⟨G,C,hGa,hG0,hlocal⟩ := exists_analytic_matrixKTransform_stable_branch_agrees_upper
    ν hν α hα F hF S hS hgap hpos u hK
  obtain ⟨ε,hε,hεlocal⟩ := Metric.mem_nhds_iff.mp hlocal
  let r := ε/4
  have hr : 0<r := div_pos hε (by norm_num)
  apply notMem_support_of_im_cauchyKernel_le_mul (μ : Measure ℝ) u r (max C ((r⁻¹)^2)) hr
  intro x hx γ hγ
  have hg : 0<(γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  let z : ℂ := (x : ℂ)+(γ : ℝ)*Complex.I
  have hz : 0<z.im := by simpa only [z,Complex.add_im,Complex.ofReal_im,
    Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
    zero_mul,add_zero,zero_add] using hg
  rw [← hμ z hz]
  by_cases hsmall : (γ : ℝ)<r
  · have hxN : |x-u|<r := by simpa only [mem_ball,Real.dist_eq] using hx
    have hdist : dist z (u : ℂ)<ε := by
      rw [dist_eq_norm]
      have he : z-(u : ℂ)=((x-u : ℝ) : ℂ)+(γ : ℝ)*Complex.I := by
        dsimp only [z]
        push_cast
        ring
      rw [he]
      have hn := norm_add_le (((x-u : ℝ) : ℂ)) (((γ : ℝ) : ℂ)*Complex.I)
      rw [norm_mul,Complex.norm_real,Complex.norm_real,Complex.norm_I,mul_one,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hg] at hn
      have hrε : 2*r<ε := by dsimp only [r]; linarith
      exact hn.trans_lt (by linarith)
    have hN := (hεlocal hdist hz).2
    have htrace := im_normalizedTrace_le_specNorm_imaginaryPart (α•F z)
    rw [specNorm_eq_norm] at htrace
    have hzγ : z.im=(γ : ℝ) := by simp [z]
    apply (htrace.trans hN).trans
    rw [hzγ]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hg.le
  · have hrg : r≤(γ : ℝ) := le_of_not_gt hsmall
    have htarget : (α*(γ : ℝ))•(1 : M)≤α•(imaginaryPart (z•(1 : M)) : M) := by
      rw [stableGap_scalar_im,smul_smul]
      simp only [z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
        add_zero,zero_add,le_refl]
    have hFN := specNorm_of_matrixKTransform_solution_le_inv ν hν α hα (z•1)
      (F z) (hF z hz).1 (hF z hz).2 (α*(γ : ℝ)) (mul_pos hα hg) htarget
    have hN : ‖α•F z‖≤(γ : ℝ)⁻¹ := by
      rw [norm_smul,Real.norm_of_nonneg hα.le]
      calc
        _ ≤ α*(α*(γ : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left (by simpa only [specNorm_eq_norm] using hFN) hα.le
        _ = _ := by field_simp [hα.ne',hg.ne']
    have htail : (γ : ℝ)⁻¹≤(r⁻¹)^2*(γ : ℝ) := by
      rw [inv_pow]
      calc
        _ = 1/(γ : ℝ) := by rw [one_div]
        _ ≤ (γ : ℝ)/r^2 := (div_le_div_iff₀ hg (sq_pos_of_pos hr)).mpr (by
          nlinarith [mul_le_mul hrg hrg hr.le hg.le])
        _ = _ := by rw [div_eq_mul_inv,mul_comm]
    calc
      _ ≤ ‖normalizedTrace (α•F z)‖ := Complex.im_le_norm _
      _ ≤ ‖α•F z‖ := by simpa only [specNorm_eq_norm] using norm_normalizedTrace_le_specNorm (α•F z)
      _ ≤ (γ : ℝ)⁻¹ := hN
      _ ≤ (r⁻¹)^2*(γ : ℝ) := htail
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hg.le

end NLAlib
