import NLAlib.Matrix.Functions.KTransformCompactStieltjesLaw
import NLAlib.Matrix.Functions.StieltjesTraceSupport
import NLAlib.ForMathlib.Analysis.Matrix.StieltjesRealContinuation

/-! # The native real K branch below the actual Stieltjes support

Actual positive quadratic measures reconstruct a real analytic matrix
continuation. Their true supports lie in the normalized trace support,
so both the matrix value and its derivative are strictly positive.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- The actual nonlinear upper-half-plane K branch has a genuine real
analytic matrix continuation below its characterized trace law. Both
its value and its derivative are positive definite. No real branch,
sample denominator, gap, or boundary derivative is assumed.
Source: Montanari--Saeed (2026), real-gap converse in Theorem 3.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_global_posDef_real_stieltjes_extension_matrixKTransform
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ)) :
    ∃ G : ℂ → M,
      (∀ z : ℂ, 0<z.im → G z=α•F z) ∧
      (∀ x : ℝ, (G x).IsHermitian) ∧
      ∀ u : ℝ, (∀ t ∈ (μ : Measure ℝ).support, u<t) →
        AnalyticAt ℂ G (u : ℂ) ∧ (G u).PosDef ∧ (deriv G (u : ℂ)).PosDef := by
  classical
  let N : ℂ → M := fun z => α•F z
  have hNa : AnalyticOnNhd ℂ N {z : ℂ | 0<z.im} :=
    fun z hz => (hFa z hz).const_smul (c := α)
  have hNp : ∀ z : ℂ, 0<z.im → (imaginaryPart (N z) : M).PosSemidef := by
    intro z hz
    have hp := ((hF z hz).1.smul hα).posSemidef
    simpa only [N,map_smul,selfAdjoint.val_smul] using hp
  obtain ⟨R0,hR0⟩ := hν.isBounded.exists_norm_le
  let R := max R0 1
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ T ∈ ν.support, specNorm T.val≤R := by
    intro T hT
    have hn : specNorm T.val≤R0 := by
      simpa only [specNorm_eq_norm,← AddSubgroup.norm_coe] using hR0 T hT
    exact hn.trans (le_max_left _ _)
  let κ := 4*(α+1)*R/α
  have hb : ∀ a : ℝ, κ<a → ∃ C : ℝ, ∀ z : ℂ, 0<z.im → a≤|z.re| →
      ‖(imaginaryPart (N z) : M)‖≤C*z.im := by
    intro a ha
    refine ⟨2*α^2*(((α+1)*R)⁻¹)^2,?_⟩
    intro z hz hza
    have ha' : 4*(α+1)*R<a*α := (div_lt_iff₀ hα).mp ha
    have hfar : 4*(α+1)*R<α*|z.re| := by
      nlinarith [mul_le_mul_of_nonneg_left hza hα.le]
    exact norm_imaginaryPart_matrixKTransform_solution_le_exterior ν hν α R hα hR F
      hFa hF hbound z hz hfar
  have hs (v : n → ℂ) :=
    (Matrix.existsUnique_finiteMeasure_quadratic_stieltjes_eq N hNa hNp
      (tendsto_mul_I_smul_matrixKTransform_solution ν hν α hα F hF) κ hb v).exists
  choose ρ hρ using hs
  have hrep (v : n → ℂ) : ∀ z : ℂ, 0<z.im → matrixQuadraticFormCLM v (N z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(ρ v : Measure ℝ) := (hρ v).2.2
  have hcompact (v : n → ℂ) : IsCompact (ρ v : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset (ρ v : Measure ℝ).isClosed_support
      ((ρ v : Measure ℝ).support_subset_of_isClosed isClosed_Icc (hρ v).2.1)
  have hsupp (v : n → ℂ) : (ρ v : Measure ℝ).support⊆(μ : Measure ℝ).support :=
    Matrix.support_quadratic_stieltjes_subset_trace_support N hNp μ (ρ v) v hμ (hrep v)
  have hmass (v : n → ℂ) (hv : v≠0) : (ρ v : Measure ℝ)≠0 := by
    intro hzero
    have hm : (ρ v).mass=0 := by
      apply ENNReal.coe_injective
      rw [FiniteMeasure.ennreal_mass,hzero]
      simp
    rw [(hρ v).1] at hm
    have hp : 0<((quadraticProbeMass v : ℝ) : ℂ) := by
      rw [ofReal_quadraticProbeMass]
      exact Matrix.PosDef.one.dotProduct_mulVec_pos hv
    simp only [hm,NNReal.coe_zero,Complex.ofReal_zero,lt_self_iff_false] at hp
  obtain ⟨G,hGa,hGN,hreal⟩ := Matrix.exists_global_real_matrix_extension_of_quadratic_stieltjes
    N ρ hrep hcompact
  refine ⟨G,hGN,hreal,?_⟩
  intro u hu
  have hgap (v : n → ℂ) (t : ℝ) (ht : t∈(ρ v : Measure ℝ).support) : u<t :=
    hu t (hsupp v ht)
  have hGau := hGa u (fun v t ht => (hgap v t ht).ne')
  obtain ⟨hG,hGd⟩ := Matrix.posDef_real_extension_and_deriv_of_quadratic_stieltjes
    N G ρ hrep hcompact hmass u hgap hGau hGN hreal
  exact ⟨hGau,hG,hGd⟩

/-- At every point below the actual normalized-trace law, the native
nonlinear K branch has an actual analytic Hermitian continuation with
positive value and derivative. Both conclusions follow from the
constructed global Stieltjes continuation.
Source: Montanari--Saeed (2026), real-gap converse in Theorem 3.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_posDef_real_stieltjes_extension_matrixKTransform
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ))
    (u : ℝ) (hu : ∀ t ∈ (μ : Measure ℝ).support, u<t) :
    ∃ G : ℂ → M, AnalyticAt ℂ G (u : ℂ) ∧
      (∀ z : ℂ, 0<z.im → G z=α•F z) ∧
      (∀ x : ℝ, (G x).IsHermitian) ∧ (G u).PosDef ∧ (deriv G (u : ℂ)).PosDef := by
  obtain ⟨G,hGN,hreal,hG⟩ :=
    exists_global_posDef_real_stieltjes_extension_matrixKTransform ν hν α hα F hFa hF μ hμ
  exact ⟨G,(hG u hu).1,hGN,hreal,(hG u hu).2⟩

end NLAlib
