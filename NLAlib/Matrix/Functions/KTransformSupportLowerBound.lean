import NLAlib.Matrix.Functions.KTransformOrderedContinuation
import NLAlib.Matrix.Functions.KTransformStableGap
import NLAlib.Matrix.Functions.KTransformCompactStieltjesLaw
import NLAlib.Matrix.Spectral.HermitianMinimum

/-! # Actual lower spectral bounds from general stable K points

Native order continuation reaches every smaller scalar target. The true
Stieltjes-law branch then excludes the whole lower half-line, so a
stable point yields a global support bound rather than one isolated gap.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- A genuine stable K point gives a lower bound on every point of the
actual characterized Stieltjes law, including nonscalar stable points.
The entire lower half-line is excluded using constructed ordered
solutions, so neither an order-image conclusion nor a support bound is
assumed.
Source: Montanari--Saeed (2026), Theorem 1, forward edge inequality (40)--(42).
atlas: block-wishart-variational-edges (partial) -/
theorem support_subset_Ici_lambdaMin_matrixKTransform_of_stable
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ))
    (S : M) (hS : S∈matrixKStableDomain ν α) :
    (μ : Measure ℝ).support⊆Ici (lambdaMin (matrixKTransform ν α S)) := by
  have hdom : S∈matrixKTransformDomain ν :=
    ⟨hS.1.isUnit,fun T hT => isUnit_matrixKDenominator S T.val hS.1 (hS.2.1 T hT)⟩
  have hKH : (matrixKTransform ν α S).IsHermitian := by
    have hs := matrixKTransform_conjTranspose ν α S hdom
    rw [hS.1.isHermitian.eq] at hs
    exact hs.symm
  obtain ⟨Y,hY,hYS⟩ := (show S∈
    (fun Y : selfAdjoint M => Y.val⁻¹) '' matrixKInverseStableDomain ν α by
      rwa [image_inverse_matrixKInverseStableDomain ν hν α hα])
  change Y.val⁻¹=S at hYS
  intro x hx
  by_contra hn
  have hlt : x<lambdaMin (matrixKTransform ν α S) := lt_of_not_ge hn
  let H : M := matrixKTransform ν α S-(x : ℂ)•1
  have hH : H.PosDef := by
    have hp := hKH.posDef_sub_smul_one_of_lt_lambdaMin hlt
    exact hp
  obtain ⟨Z,_hZY,hZ,hKZ⟩ :=
    exists_ordered_matrixKTransform_inverse_solution ν hν α hα Y hY H hH
  have hst : Z.val⁻¹∈matrixKStableDomain ν α := by
    rw [← image_inverse_matrixKInverseStableDomain ν hν α hα]
    exact ⟨Z,hZ,rfl⟩
  have hscalar : matrixKTransform ν α Z.val⁻¹=(x : ℂ)•1 := by
    rw [hKZ,hYS]
    dsimp only [H]
    abel
  exact (notMem_support_of_matrixKTransform_stable_solution ν hν α hα F hF μ hμ
    Z.val⁻¹ hst.1 hst.2.1 hst.2.2 x hscalar) hx

/-- The original compact sample law constructs its compactly
supported probability law whose lower edge dominates every general
stable-point objective. This is the genuine forward variational bound,
with the law, branch and support bound all derived from the original
nonlinear K equation.
Source: Montanari--Saeed (2026), Theorem 1, inequality (40)--(42).
atlas: block-wishart-variational-edges (partial) -/
theorem exists_compact_matrixKTransform_law_lower_edge_bound
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) :
    ∃ F : ℂ → M, AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} ∧
      (∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
        matrixKTransform ν α (F z)=z•1) ∧
      ∃ μ : FiniteMeasure ℝ, μ.mass=1 ∧ IsCompact (μ : Measure ℝ).support ∧
        (∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
          ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ)) ∧
        ∀ S : M, S∈matrixKStableDomain ν α →
          lambdaMin (matrixKTransform ν α S)≤sInf (μ : Measure ℝ).support := by
  obtain ⟨F,hFa,hF,μ,hμ,_huniq⟩ :=
    exists_analytic_matrixKTransform_compact_stieltjes_probability_measure ν hν α hα
  have hne : (μ : Measure ℝ)≠0 := by
    intro hz
    have hm : μ.mass=0 := by
      apply ENNReal.coe_injective
      rw [FiniteMeasure.ennreal_mass,hz]
      simp
    rw [hμ.1] at hm
    exact one_ne_zero hm
  refine ⟨F,hFa,hF,μ,hμ.1,hμ.2.1,hμ.2.2,?_⟩
  intro S hS
  exact le_csInf (Measure.nonempty_support hne) fun x hx =>
    support_subset_Ici_lambdaMin_matrixKTransform_of_stable ν hν α hα F hF μ hμ.2.2 S hS hx
end NLAlib
