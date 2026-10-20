import NLAlib.Matrix.Functions.KTransformAffineBranch
import NLAlib.Matrix.Functions.KTransformStableOpen
import NLAlib.Matrix.Functions.KTransformSubsolution

/-! # Actual geometry of the stable K-transform image

Local analytic inversion and openness of the original stable domain give
a genuine positive scalar target increase through every stable point.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- Every original stable K target admits a genuine positive scalar
increase, with a constructed preimage in the same original stable domain.
Actual local inversion and domain openness prove both conclusions.
Source: Montanari--Saeed (2026), stable K-domain local inversion.
atlas: block-wishart-log-potential (partial) -/
theorem exists_stable_matrixKTransform_scalar_increase
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (S : M) (hS : S ∈ matrixKStableDomain ν α) :
    ∃ (ε : ℝ) (Q : M), 0 < ε ∧ Q ∈ matrixKStableDomain ν α ∧
      matrixKTransform ν α Q = matrixKTransform ν α S + ε • (1 : M) := by
  obtain ⟨G, B, hGa, hG0, _hB, _hGd, hGH, hGeq⟩ :=
    exists_analytic_matrixKTransform_decreasing_affine_branch ν hν α hα
      S hS.1 hS.2.1 hS.2.2 1 Matrix.PosDef.one
  have hx : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hGlim : Tendsto (fun t : ℝ => G t) (𝓝 0) (𝓝 S) := by
    simpa only [Function.comp_def, hG0] using hGa.continuousAt.tendsto.comp hx
  let Ssa : selfAdjoint M := ⟨S, hS.1.isHermitian⟩
  have hpartS : selfAdjointPart ℝ S = Ssa :=
    Subtype.ext (hS.1.isHermitian.isSelfAdjoint.coe_selfAdjointPart_apply ℝ)
  have hRlim : Tendsto (fun t : ℝ => selfAdjointPart ℝ (G t)) (𝓝 0) (𝓝 Ssa) := by
    simpa only [Function.comp_def, hpartS] using
      (continuous_selfAdjointPart ℝ M).tendsto S |>.comp hGlim
  have hstay := hRlim.eventually
    ((isOpen_matrixKStableDomain_hermitian ν hν α hα).mem_nhds hS)
  have hstable : ∀ᶠ t : ℝ in 𝓝 0, G t ∈ matrixKStableDomain ν α := by
    filter_upwards [hstay, hGH] with t ht hHt
    change (selfAdjointPart ℝ (G t) : M) ∈ matrixKStableDomain ν α at ht
    rwa [hHt.isSelfAdjoint.coe_selfAdjointPart_apply ℝ] at ht
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hnegC : Tendsto (fun t : ℝ => ((-t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hneg
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧
      G ((-t : ℝ) : ℂ) ∈ matrixKStableDomain ν α ∧
      matrixKTransform ν α (G ((-t : ℝ) : ℂ)) = matrixKTransform ν α S + t • (1 : M) := by
    filter_upwards [self_mem_nhdsWithin, hneg.eventually hstable, hnegC.eventually hGeq]
      with t ht hst hsolve
    refine ⟨ht, hst, ?_⟩
    have hsm : (t : ℂ) • (1 : M) = t • (1 : M) := IsScalarTower.algebraMap_smul ℂ t 1
    simpa only [Complex.ofReal_neg, neg_smul, sub_neg_eq_add, hsm] using hsolve.2
  obtain ⟨t, ht, hst, hsolve⟩ := he.exists
  exact ⟨t, G ((-t : ℝ) : ℂ), ht, hst, hsolve⟩

/-- The image of the original stable K domain is genuinely convex.
Actual local target increases make inverse-variable convex combinations
strict subsolutions, and the constructed monotone fixed point supplies
their actual stable preimages. Image convexity is a conclusion.
Source: inverse-variable concavity route for Montanari--Saeed (2026).
atlas: block-wishart-log-potential (partial) -/
theorem convex_image_matrixKTransform_stableDomain
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) :
    Convex ℝ ((matrixKTransform ν α) '' matrixKStableDomain ν α) := by
  rintro U ⟨S, hS, rfl⟩ V ⟨Q, hQ, rfl⟩ a b ha hb hab
  obtain ⟨ε, P, hε, hP, hKP⟩ := exists_stable_matrixKTransform_scalar_increase
    ν hν α hα S hS
  obtain ⟨η, R, hη, hR, hKR⟩ := exists_stable_matrixKTransform_scalar_increase
    ν hν α hα Q hQ
  let Y := P⁻¹
  let Z := R⁻¹
  have hY : Y.PosDef := hP.1.inv
  have hZ : Z.PosDef := hR.1.inv
  have hYY : Y⁻¹ = P := Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hP.1.isUnit)
  have hZZ : Z⁻¹ = R := Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hR.1.isUnit)
  have hgapY : ∀ T ∈ ν.support, (Y + T.val).PosDef := hP.2.1
  have hgapZ : ∀ T ∈ ν.support, (Z + T.val).PosDef := hR.2.1
  obtain ⟨hW, hgapW⟩ := posDef_add_samples_of_convex_combination
    ν Y Z hY hZ hgapY hgapZ ha hb hab
  let W : selfAdjoint M := ⟨a • Y + b • Z, hW.isHermitian⟩
  let L := a • matrixKTransform ν α S + b • matrixKTransform ν α Q
  have hδ : 0 < a * ε + b * η := by
    rcases ha.eq_or_lt with ha0 | ha0
    · have hae : a = 0 := ha0.symm
      have hbe : b = 1 := by linarith
      simpa only [hae, hbe, zero_mul, one_mul, zero_add] using hη
    · exact add_pos_of_pos_of_nonneg (mul_pos ha0 hε) (mul_nonneg hb hη.le)
  have hconc := smul_add_smul_matrixKTransform_inverse_le
    ν hν α Y Z hY hZ hgapY hgapZ ha hb hab
  rw [hYY, hZZ, hKP, hKR] at hconc
  have he : a • (matrixKTransform ν α S + ε • (1 : M)) +
      b • (matrixKTransform ν α Q + η • (1 : M)) = L + (a * ε + b * η) • (1 : M) := by
    dsimp only [L]
    module
  rw [he] at hconc
  have hle : (a * ε + b * η) • (1 : M) ≤ matrixKTransform ν α W.val⁻¹ - L := by
    convert sub_le_sub_right hconc L using 1; abel
  have hdec : (matrixKTransform ν α W.val⁻¹ - L).PosDef :=
    ((Matrix.PosDef.one.smul hδ).isStrictlyPositive.of_le hle).posDef
  obtain ⟨J, _horder, hJ, hKJ⟩ :=
    exists_stable_matrixKTransform_inverse_solution_of_strict_subsolution ν hν α hα
      W hW hgapW L hdec
  have hst : J.val⁻¹ ∈ matrixKStableDomain ν α := by
    rw [← image_inverse_matrixKInverseStableDomain ν hν α hα]
    exact ⟨J, hJ, rfl⟩
  exact ⟨J.val⁻¹, hst, hKJ⟩

end NLAlib
