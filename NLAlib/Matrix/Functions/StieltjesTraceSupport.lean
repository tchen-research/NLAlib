import NLAlib.ForMathlib.Analysis.Matrix.HerglotzScalar
import NLAlib.Matrix.Norms.PositiveImaginaryTrace
import NLAlib.ForMathlib.MeasureTheory.StieltjesTestGap

/-! # A positive matrix Herglotz function has no hidden probe support

The true PSD trace dominates every scalar quadratic imaginary part.
A gap of the actual normalized-trace law is therefore a gap for every
actual quadratic Stieltjes measure, with no measure domination premise.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter Metric
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- A true quadratic Stieltjes measure of a positive-imaginary matrix
function is supported inside its actual normalized-trace Stieltjes
support. This proves the support bridge from positivity and actual
integrals, rather than assuming measure domination. -/
theorem support_quadratic_stieltjes_subset_trace_support
    (N : ℂ → M)
    (hN : ∀ z : ℂ, 0<z.im → (imaginaryPart (N z) : M).PosSemidef)
    (μ ρ : FiniteMeasure ℝ) (v : n → ℂ)
    (hμ : ∀ z : ℂ, 0<z.im → NLAlib.normalizedTrace (N z)=
      ∫ ξ : ℝ, ((ξ : ℂ)-z)⁻¹ ∂(μ : Measure ℝ))
    (hρ : ∀ z : ℂ, 0<z.im → matrixQuadraticFormCLM v (N z)=
      ∫ ξ : ℝ, ((ξ : ℂ)-z)⁻¹ ∂(ρ : Measure ℝ)) :
    (ρ : Measure ℝ).support⊆(μ : Measure ℝ).support := by
  intro x hx
  by_contra hnot
  obtain ⟨ε,hε,hεsub⟩ := Metric.isOpen_iff.mp (μ : Measure ℝ).isClosed_support.isOpen_compl x hnot
  let r := ε/2
  have hr : 0<r := half_pos hε
  have hsepx : ∀ᵐ ξ : ℝ ∂(μ : Measure ℝ), ε≤|ξ-x| := by
    filter_upwards [(μ : Measure ℝ).support_mem_ae] with ξ hξ
    apply le_of_not_gt
    intro hh
    have hball : ξ∈ball x ε := by simpa only [mem_ball,Real.dist_eq] using hh
    exact (hεsub hball) hξ
  apply (notMem_support_of_im_cauchyKernel_le_mul (ρ : Measure ℝ) x r
    (‖matrixRealQuadraticFormCLM v‖*(Fintype.card n : ℝ)*
      (r⁻¹)^2*(μ.mass : ℝ)) hr ?_) hx
  intro y hy γ hγ
  have hγpos : 0<(γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  let z : ℂ := (y : ℂ)+(γ : ℝ)*Complex.I
  have hz : 0<z.im := by simpa [z] using hγpos
  have hsep : ∀ᵐ ξ : ℝ ∂(μ : Measure ℝ), r≤|ξ-y| := by
    filter_upwards [hsepx] with ξ hξ
    have hy' : |y-x|<r := by simpa only [mem_ball,Real.dist_eq] using hy
    have htri : |ξ-x|≤|ξ-y|+|y-x| := by
      simpa only [sub_add_sub_cancel] using abs_add_le (ξ-y) (y-x)
    dsimp only [r] at *
    linarith
  have hmuBound := im_integral_real_cauchyKernel_le_of_ae_dist_ge (μ : Measure ℝ) y r hr γ hγ hsep
  have hmuBound' : (NLAlib.normalizedTrace (N z)).im≤
      (r⁻¹)^2*(μ.mass : ℝ)*(γ : ℝ) := by
    rw [hμ z hz]
    have hm : (μ : Measure ℝ).real univ=(μ.mass : ℝ) := by
      rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
    rw [hm] at hmuBound
    convert! hmuBound using 1
    simp only [div_eq_mul_inv,inv_pow]
    ring
  rw [← hρ z hz,im_matrixQuadraticFormCLM]
  calc
    _ ≤ ‖matrixRealQuadraticFormCLM v (imaginaryPart (N z) : M)‖ := le_abs_self _
    _ ≤ ‖matrixRealQuadraticFormCLM v‖*‖(imaginaryPart (N z) : M)‖ :=
      (matrixRealQuadraticFormCLM v).le_opNorm _
    _ ≤ ‖matrixRealQuadraticFormCLM v‖*((Fintype.card n : ℝ)*
        (NLAlib.normalizedTrace (N z)).im) :=
      mul_le_mul_of_nonneg_left (norm_imaginaryPart_le_card_mul_im_normalizedTrace (N z) (hN z hz))
        (norm_nonneg _)
    _ ≤ ‖matrixRealQuadraticFormCLM v‖*((Fintype.card n : ℝ)*
        ((r⁻¹)^2*(μ.mass : ℝ)*(γ : ℝ))) := by gcongr
    _ = _ := by ring

end Matrix
