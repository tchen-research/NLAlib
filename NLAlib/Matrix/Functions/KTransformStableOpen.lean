import NLAlib.Matrix.Functions.KTransformStableDomain
import NLAlib.Matrix.Functions.KTransformComplexCalculus

/-!
# Relative openness of the actual stable K-domain

Strict positivity is stable under small Hermitian perturbations. Compact
support makes the original positive denominator gaps simultaneous, and
continuity of the actual derivative preserves a genuine positive witness.
Source: Montanari--Saeed (2026), Lemma 9.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology

namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

private theorem eventually_posDef_of_continuousAt
    {X : Type*} [TopologicalSpace X] {f : X → Matrix n n ℂ} {x : X}
    (hf : ContinuousAt f x) (hfx : (f x).PosDef)
    (hH : ∀ᶠ y in 𝓝 x, (f y).IsHermitian) :
    ∀ᶠ y in 𝓝 x, (f y).PosDef := by
  obtain ⟨δ,hδ,hδf⟩ : ∃ δ : ℝ, 0<δ ∧ δ•(1 : Matrix n n ℂ) ≤ f x := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CFC.exists_pos_algebraMap_le_iff hfx.isHermitian.isSelfAdjoint).mpr
        (fun r hr => hfx.isStrictlyPositive.spectrum_pos hr)
  have hs : ∀ᶠ y in 𝓝 x, ‖f y-f x‖<δ :=
    ((hf.sub_const (f x)).norm).eventually_lt continuousAt_const (by simpa using hδ)
  filter_upwards [hs,hH] with y hy hHy
  have hneg : (-‖f y-f x‖)•(1 : Matrix n n ℂ) ≤ f y-f x := by
    simpa only [Algebra.algebraMap_eq_smul_one,neg_smul] using
      (hHy.sub hfx.isHermitian).isSelfAdjoint.neg_algebraMap_norm_le_self
  have hle : (δ-‖f y-f x‖)•(1 : Matrix n n ℂ) ≤ f y := by
    convert! add_le_add hδf hneg using 1 <;> module
  exact ((Matrix.PosDef.one.smul (sub_pos.mpr hy)).isStrictlyPositive.of_le hle).posDef

private theorem eventually_matrixK_positive_gaps
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (hν : IsCompact ν.support)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : S.val.PosDef)
    (hgap : ∀ T ∈ ν.support, (S.val⁻¹+T.val).PosDef) :
    ∀ᶠ X : selfAdjoint (Matrix n n ℂ) in 𝓝 S,
      X.val.PosDef ∧ ∀ T ∈ ν.support, (X.val⁻¹+T.val).PosDef := by
  have hp : ∀ᶠ X : selfAdjoint (Matrix n n ℂ) in 𝓝 S, X.val.PosDef :=
    eventually_posDef_of_continuousAt continuous_subtype_val.continuousAt hS
      (Eventually.of_forall fun X => X.property)
  have hg : ∀ᶠ X : selfAdjoint (Matrix n n ℂ) in 𝓝 S,
      ∀ T ∈ ν.support, (X.val⁻¹+T.val).PosDef := by
    apply hν.eventually_forall_of_forall_eventually
    intro T hT
    have hi : ContinuousAt
        (fun p : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ) => p.1.val⁻¹)
        (S,T) :=
      (hasFDerivAt_matrixInverse S.val hS.isUnit).continuousAt.comp
        (f := fun p : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ) => p.1.val)
        (continuous_subtype_val.comp continuous_fst).continuousAt
    have hf := hi.add (continuous_subtype_val.comp continuous_snd).continuousAt
    apply eventually_posDef_of_continuousAt hf (hgap T hT)
    exact Eventually.of_forall fun p =>
      (show p.1.val.IsHermitian from p.1.property).inv.add p.2.property
  exact hp.and hg

private theorem quadratic_pos_iff_derivative_witness
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α)
    (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef) :
    (∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ≠0 →
      0<frobInner Δ (matrixKTransformDeriv ν α S Δ)) ↔
    ∃ B : Matrix n n ℂ, B.PosDef ∧ (matrixKTransformDeriv ν α S B).PosDef := by
  rw [matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα S hS hgap,
    matrixKTransform_norm_iff_supersolution ν hν α hα S hS hgap,
    matrixKTransform_supersolution_iff_derivative_witness ν hν α hα S hS hgap]

/-- The actual original source stable K-domain is open relative to the
Hermitian matrix space. Compactness preserves every support-only positive
gap simultaneously, and continuity of the actual derivative preserves a
derived positive witness. Combined with `isConnected_matrixKStableDomain`,
this proves the topological assertions of source Lemma 9.
Source: Montanari--Saeed (2026), Lemma 9.
atlas: block-wishart-variational-edges (partial) -/
theorem isOpen_matrixKStableDomain_hermitian
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0<α) :
    IsOpen {S : selfAdjoint (Matrix n n ℂ) | S.val ∈ matrixKStableDomain ν α} := by
  apply isOpen_iff_mem_nhds.mpr
  intro S hS
  obtain ⟨B,hB,hDB⟩ :=
    (quadratic_pos_iff_derivative_witness ν hν α hα S.val hS.1 hS.2.1).mp hS.2.2
  have hd : S.val ∈ matrixKTransformDomain ν :=
    ⟨hS.1.isUnit,fun T hT => isUnit_matrixKDenominator S.val T.val hS.1 (hS.2.1 T hT)⟩
  have hg := eventually_matrixK_positive_gaps ν hν S hS.1 hS.2.1
  have hc : ContinuousAt
      (fun X : selfAdjoint (Matrix n n ℂ) => matrixKTransformDeriv ν α X.val B) S := by
    have hh := ((continuousAt_matrixKTransformDerivComplex ν hν α hd).comp
      (f := fun X : selfAdjoint (Matrix n n ℂ) => X.val)
      continuous_subtype_val.continuousAt).clm_apply (continuousAt_const (y := B))
    change ContinuousAt
      (fun X : selfAdjoint (Matrix n n ℂ) => matrixKTransformDerivComplex ν α X.val B) S at hh
    have he : (fun X : selfAdjoint (Matrix n n ℂ) => matrixKTransformDerivComplex ν α X.val B) =
        (fun X : selfAdjoint (Matrix n n ℂ) => matrixKTransformDeriv ν α X.val B) := by
      funext X
      exact congrArg (fun D : Matrix n n ℂ →L[ℝ] Matrix n n ℂ => D B)
        (matrixKTransformDerivComplex_restrictScalars ν α X.val)
    rwa [he] at hh
  have hHerm : ∀ᶠ X : selfAdjoint (Matrix n n ℂ) in 𝓝 S,
      (matrixKTransformDeriv ν α X.val B).IsHermitian := by
    filter_upwards [hg] with X hX
    exact isHermitian_matrixKTransformDeriv ν hν α hα X.val hX.1 hX.2 hB.isHermitian
  have hpos := eventually_posDef_of_continuousAt hc hDB hHerm
  filter_upwards [hg,hpos] with X hX hDX
  exact ⟨hX.1,hX.2,
    (quadratic_pos_iff_derivative_witness ν hν α hα X.val hX.1 hX.2).mpr ⟨B,hB,hDX⟩⟩

end NLAlib
