import NLAlib.Matrix.Functions.KTransformSupportLowerBound
import NLAlib.Matrix.Functions.KTransformRealStieltjesBranch

/-! # Actual stable real points and the Stieltjes continuation

Upper-half-plane uniqueness and genuine boundary continuity identify
the independently constructed real branches. Native stable-domain
nonemptiness and ordered continuation supply a scalar real seed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- At a genuine stable scalar K point the actual Stieltjes matrix
continuation equals the source real inverse branch. Equality follows
from native upper-half-plane uniqueness and true boundary limits.
Source: Montanari--Saeed (2026), Theorem 3, real branch identification.
atlas: block-wishart-variational-edges (partial) -/
theorem eq_real_stieltjes_extension_at_stable_matrixKTransform_solution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (G : ℂ → M) (u : ℝ) (hGa : AnalyticAt ℂ G (u : ℂ))
    (hGN : ∀ z : ℂ, 0<z.im → G z=α•F z)
    (S : M) (hS : S∈matrixKStableDomain ν α)
    (hK : matrixKTransform ν α S=(u : ℂ)•1) : G u=α•S := by
  obtain ⟨H,C,hHa,hH0,hlocal⟩ := exists_analytic_matrixKTransform_stable_branch_agrees_upper
    ν hν α hα F hF S hS.1 hS.2.1 hS.2.2 u hK
  let φ : ℝ → ℂ := fun y => (u : ℂ)+(y : ℂ)*Complex.I
  have hφc : Continuous φ := by fun_prop
  have hφ : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 (u : ℂ)) := by
    simpa only [φ,Complex.ofReal_zero,zero_mul,add_zero] using
      (hφc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ y : ℝ in 𝓝[>] 0, G (φ y)=α•H (φ y) := by
    filter_upwards [hφ.eventually hlocal,self_mem_nhdsWithin] with y hy hyp
    have hz : 0<(φ y).im := by simpa [φ] using (show 0<y from hyp)
    rw [hGN _ hz,(hy hz).1]
  have hGlim := hGa.continuousAt.tendsto.comp hφ
  have hHlim : Tendsto (fun y : ℝ => α•H (φ y)) (𝓝[>] 0) (𝓝 (α•S)) := by
    simpa only [Function.comp_def,hH0] using
      (hHa.continuousAt.tendsto.comp hφ).const_smul α
  exact tendsto_nhds_unique hGlim (hHlim.congr' (he.mono fun y hy => hy.symm))

/-- The actual compact sample law has a genuine stable scalar point
strictly below the whole characterized trace support, and the actual
real Stieltjes branch equals that stable solution there. This seed is
constructed by the proved native stable domain and ordered inverse;
no far-left real branch or stable point is assumed.
Source: Montanari--Saeed (2026), Theorem 3, lower-component seed.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_matrixKTransform_stable_scalar_stieltjes_seed
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ))
    (G : ℂ → M)
    (hGa : ∀ u : ℝ, (∀ t ∈ (μ : Measure ℝ).support, u<t) → AnalyticAt ℂ G (u : ℂ))
    (hGN : ∀ z : ℂ, 0<z.im → G z=α•F z) :
    ∃ (u : ℝ) (S : M),
      (∀ t ∈ (μ : Measure ℝ).support, u+1≤t) ∧
      S∈matrixKStableDomain ν α ∧ matrixKTransform ν α S=(u : ℂ)•1 ∧ G u=α•S := by
  obtain ⟨S0,hS0⟩ := (isConnected_matrixKStableDomain ν hν α hα).nonempty
  have hdom : S0∈matrixKTransformDomain ν :=
    ⟨hS0.1.isUnit,fun T hT => isUnit_matrixKDenominator S0 T.val hS0.1 (hS0.2.1 T hT)⟩
  have hKH : (matrixKTransform ν α S0).IsHermitian := by
    have hs := matrixKTransform_conjTranspose ν α S0 hdom
    rw [hS0.1.isHermitian.eq] at hs
    exact hs.symm
  let u := lambdaMin (matrixKTransform ν α S0)-1
  let H : M := matrixKTransform ν α S0-(u : ℂ)•1
  have hH : H.PosDef := hKH.posDef_sub_smul_one_of_lt_lambdaMin (by
    change lambdaMin (matrixKTransform ν α S0)-1 < lambdaMin (matrixKTransform ν α S0)
    linarith)
  have hYS : S0∈(fun Y : selfAdjoint M => Y.val⁻¹) '' matrixKInverseStableDomain ν α := by
    rwa [image_inverse_matrixKInverseStableDomain ν hν α hα]
  obtain ⟨Y,hY,hYS⟩ := hYS
  change Y.val⁻¹=S0 at hYS
  obtain ⟨Z,_hZY,hZ,hKZ⟩ :=
    exists_ordered_matrixKTransform_inverse_solution ν hν α hα Y hY H hH
  have hst : Z.val⁻¹∈matrixKStableDomain ν α := by
    rw [← image_inverse_matrixKInverseStableDomain ν hν α hα]
    exact ⟨Z,hZ,rfl⟩
  have hscalar : matrixKTransform ν α Z.val⁻¹=(u : ℂ)•1 := by
    rw [hKZ,hYS]
    dsimp only [H]
    abel
  have hmargin : ∀ t ∈ (μ : Measure ℝ).support, u+1≤t := by
    intro t ht
    have hh := support_subset_Ici_lambdaMin_matrixKTransform_of_stable
      ν hν α hα F hF μ hμ S0 hS0 ht
    change lambdaMin (matrixKTransform ν α S0)≤t at hh
    change lambdaMin (matrixKTransform ν α S0)-1+1≤t
    linarith
  have hgap : ∀ t ∈ (μ : Measure ℝ).support, u<t := by
    intro t ht
    linarith [hmargin t ht]
  refine ⟨u,Z.val⁻¹,hmargin,hst,hscalar,?_⟩
  exact eq_real_stieltjes_extension_at_stable_matrixKTransform_solution
    ν hν α hα F hF G u (hGa u hgap) hGN Z.val⁻¹ hst hscalar

end NLAlib
