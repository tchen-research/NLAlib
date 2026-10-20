import NLAlib.Matrix.Functions.KTransformLowerRealInverse

/-! # Native lower-edge variational formula

The forward support bound and the actual stable scalar inverse at
every point of the lower trace gap identify the supremum exactly.
The equivalent finite positive derivative witness is proved using the
native source stability equivalences.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

private theorem lambdaMin_real_smul_one (u : ℝ) : lambdaMin ((u : ℂ)•(1 : M))=u := by
  have he : (u : ℂ)•(1 : M)=algebraMap ℝ M u := by
    rw [Algebra.algebraMap_eq_smul_one]
    ext i j
    simp only [Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,smul_eq_mul]
    rfl
  rw [he,lambdaMin,spectrum.scalar_eq,csInf_singleton]

private theorem lambdaMin_pos_of_posDef {A : M} (hA : A.PosDef) : 0<lambdaMin A := by
  rw [lambdaMin_eq_eigenvalues₀_last hA.isHermitian]
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let j : Fin (Fintype.card n) := ⟨Fintype.card n-1,Nat.sub_one_lt_of_lt Fintype.card_pos⟩
  simpa [Matrix.IsHermitian.eigenvalues,e,j] using hA.eigenvalues_pos (e j)

/-- The actual lower support edge equals the supremum of the true
smallest K eigenvalue over the native strict stable region. The reverse
inequality is supplied by actual scalar stable solutions throughout
the lower trace gap. No optimizer attainment, real branch, denominator
gap, or variational conclusion is assumed.
Source: Montanari--Saeed (2026), Theorems 1 and 3.
atlas: block-wishart-variational-edges (partial) -/
theorem sInf_support_eq_sSup_lambdaMin_matrixKTransform
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ) (hmass : μ.mass=1)
    (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ)) :
    sInf (μ : Measure ℝ).support =
      sSup ((fun S : M => lambdaMin (matrixKTransform ν α S)) '' matrixKStableDomain ν α) := by
  have hne : (μ : Measure ℝ)≠0 := by
    intro hz
    have hm : μ.mass=0 := by
      apply ENNReal.coe_injective
      rw [FiniteMeasure.ennreal_mass,hz]
      simp
    rw [hmass] at hm
    exact one_ne_zero hm
  let a : ℝ := sInf (μ : Measure ℝ).support
  let A : Set ℝ := (fun S : M => lambdaMin (matrixKTransform ν α S)) '' matrixKStableDomain ν α
  have hAne : A.Nonempty :=
    (isConnected_matrixKStableDomain ν hν α hα).nonempty.image _
  have hupper : ∀ x∈A,x≤a := by
    rintro x ⟨S,hS,rfl⟩
    exact le_csInf (Measure.nonempty_support hne) fun t ht =>
      support_subset_Ici_lambdaMin_matrixKTransform_of_stable ν hν α hα F hF μ hμ S hS ht
  have hAb : BddAbove A := ⟨a,hupper⟩
  apply le_antisymm
  · apply le_of_forall_lt_imp_le_of_dense
    intro u hu
    obtain ⟨S,hS,hK⟩ := exists_stable_matrixKTransform_scalar_solution_below_trace_support
      ν hν α hα F hFa hF μ hmass hcompact hμ u
        (fun t ht => lt_of_lt_of_le hu (csInf_le hcompact.bddBelow ht))
    have he : lambdaMin (matrixKTransform ν α S)=u := by rw [hK,lambdaMin_real_smul_one]
    exact le_csSup hAb ⟨S,hS,he⟩
  · exact csSup_le hAne hupper

/-- Strict positivity of the actual limiting support is equivalent to
the original finite-matrix source witnesses: positive S and B, positive
sample gaps, a positive true derivative value DK(S)[B], and positive
K(S). All data refer to the actual characterized native law.
Source: Montanari--Saeed (2026), Corollary 1 and Theorems 1 and 3.
atlas: block-wishart-variational-edges (partial) -/
theorem sInf_support_pos_iff_exists_matrixKTransform_posDef_witness
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ) (hmass : μ.mass=1)
    (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ)) :
    0<sInf (μ : Measure ℝ).support ↔
      ∃ S B : M, S.PosDef ∧ B.PosDef ∧
        (∀ T∈ν.support,(S⁻¹+T.val).PosDef) ∧
        (matrixKTransformDeriv ν α S B).PosDef ∧ (matrixKTransform ν α S).PosDef := by
  constructor
  · intro ha
    let u := sInf (μ : Measure ℝ).support/2
    have hu : 0<u := half_pos ha
    obtain ⟨S,hS,hK⟩ := exists_stable_matrixKTransform_scalar_solution_below_trace_support
      ν hν α hα F hFa hF μ hmass hcompact hμ u
        (fun t ht => lt_of_lt_of_le (half_lt_self ha) (csInf_le hcompact.bddBelow ht))
    obtain ⟨B,hB,hD⟩ := (matrixKTransform_supersolution_iff_derivative_witness ν hν α hα S hS.1 hS.2.1).mp
      ((matrixKTransform_norm_iff_supersolution ν hν α hα S hS.1 hS.2.1).mp
        ((matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα S hS.1 hS.2.1).mp hS.2.2))
    refine ⟨S,B,hS.1,hB,hS.2.1,hD,?_⟩
    rw [hK]
    exact Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hu)
  · rintro ⟨S,B,hS,hB,hgap,hD,hK⟩
    have hst : S∈matrixKStableDomain ν α := by
      refine ⟨hS,hgap,?_⟩
      rw [matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα S hS hgap,
        matrixKTransform_norm_iff_supersolution ν hν α hα S hS hgap,
        matrixKTransform_supersolution_iff_derivative_witness ν hν α hα S hS hgap]
      exact ⟨B,hB,hD⟩
    have hne : (μ : Measure ℝ)≠0 := by
      intro hz
      have hm : μ.mass=0 := by
        apply ENNReal.coe_injective
        rw [FiniteMeasure.ennreal_mass,hz]
        simp
      rw [hmass] at hm
      exact one_ne_zero hm
    have hlow : lambdaMin (matrixKTransform ν α S)≤sInf (μ : Measure ℝ).support :=
      le_csInf (Measure.nonempty_support hne) fun t ht =>
        support_subset_Ici_lambdaMin_matrixKTransform_of_stable ν hν α hα F hF μ hμ S hst ht
    exact lt_of_lt_of_le (lambdaMin_pos_of_posDef hK) hlow

end NLAlib
