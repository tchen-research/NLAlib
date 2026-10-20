import NLAlib.Matrix.Functions.KTransformCalculus
import NLAlib.ForMathlib.MeasureTheory.CompactSupportContinuity
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Complex calculus on the actual matrix K-transform domain

Compact support gives an open domain of simultaneously invertible solved
denominators. On that genuine domain the actual K-transform is complex C1.
The complex derivative restricts to the existing real derivative exactly.
These facts are prerequisites for the block-Wishart stable inverse branch.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The genuine open inverse domain, including every solved support
denominator rather than an almost-everywhere surrogate. -/
def matrixKTransformDomain (ν : Measure (selfAdjoint (Matrix n n ℂ))) :
    Set (Matrix n n ℂ) :=
  {S | IsUnit S ∧ ∀ T ∈ ν.support, IsUnit (1 + S * T.val)}

/-- Compactness of the actual support makes simultaneous denominator
invertibility an open condition on the actual matrix variable. -/
theorem isOpen_matrixKTransformDomain
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (hν : IsCompact ν.support) :
    IsOpen (matrixKTransformDomain ν) := by
  apply isOpen_iff_mem_nhds.mpr
  intro S hS
  let U : Set (Matrix n n ℂ × selfAdjoint (Matrix n n ℂ)) :=
    {p | IsUnit (1 + p.1 * p.2.val)}
  have hU : IsOpen U := Units.isOpen.preimage
    (continuous_const.add (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨V,W,hVo,_hWo,hSV,hνW,hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := S)) hν hU
      (by rintro ⟨X,T⟩ ⟨rfl,hT⟩; exact hS.2 T hT)
  have hV : V ∩ {X : Matrix n n ℂ | IsUnit X} ∈ 𝓝 S :=
    inter_mem (hVo.mem_nhds (hSV (by simp))) (Units.isOpen.mem_nhds hS.1)
  apply mem_of_superset hV
  intro X hX
  refine ⟨hX.2,?_⟩
  intro T hT
  have ht : (X,T) ∈ U := hVW ⟨hX.1,hνW hT⟩
  exact ht

/-- The complex-linear derivative of an actual K resolvent kernel. -/
def matrixKResolventDerivComplex (S T : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  -ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)
    (matrixKResolvent S T) (matrixKResolvent S T)

/-- The genuine complex derivative candidate for the actual K-transform. -/
def matrixKTransformDerivComplex (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    (α : ℝ) (S : Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  (∫ T, matrixKResolventDerivComplex S T.val ∂ν) +
    α⁻¹ • ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) S⁻¹ S⁻¹

/-- Restricting the genuine kernel derivative to real scalars preserves its
actual matrix action. -/
theorem matrixKResolventDerivComplex_restrictScalars (S T : Matrix n n ℂ) :
    (matrixKResolventDerivComplex S T).restrictScalars ℝ = matrixKResolventDeriv S T := by
  ext X
  rfl

/-- The complex derivative restricts exactly to the existing actual real
derivative. Scalar restriction is an isometry, so this identity also holds
for the total Bochner integrals before admissibility is assumed. -/
theorem matrixKTransformDerivComplex_restrictScalars
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ) (S : Matrix n n ℂ) :
    (matrixKTransformDerivComplex ν α S).restrictScalars ℝ = matrixKTransformDeriv ν α S := by
  let L := ContinuousLinearMap.restrictScalarsIsometry ℂ (Matrix n n ℂ) (Matrix n n ℂ) ℝ ℝ
  have hI := L.integral_comp_comm (μ := ν) (fun T => matrixKResolventDerivComplex S T.val)
  change L ((∫ T, matrixKResolventDerivComplex S T.val ∂ν) +
    α⁻¹ • ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) S⁻¹ S⁻¹) = _
  rw [map_add, map_smul, ← hI]
  change (∫ T, (matrixKResolventDerivComplex S T.val).restrictScalars ℝ ∂ν) + _ = _
  simp_rw [matrixKResolventDerivComplex_restrictScalars]
  unfold matrixKTransformDeriv
  congr 1

/-- At every actual inverse-domain point, the K-transform has its genuine
complex Fréchet derivative. Support compactness supplies differentiation
under the integral; no holomorphy assumption is added. -/
theorem hasFDerivAt_matrixKTransform_complex
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ matrixKTransformDomain ν) :
    HasFDerivAt (matrixKTransform ν α) (matrixKTransformDerivComplex ν α S) S := by
  exact hasFDerivAt_of_restrictScalars ℝ
    (hasFDerivAt_matrixKTransform ν hν α S hS.1 hS.2)
    (matrixKTransformDerivComplex_restrictScalars ν α S)

private theorem continuousAt_matrixKResolventDerivComplex (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ =>
      matrixKResolventDerivComplex p.1 p.2) (S,T) := by
  have hr := continuousAt_matrixKResolvent S T h
  have hleft := (ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)).continuous.continuousAt.comp hr
  exact (hleft.clm_apply hr).neg

/-- The genuine complex derivative is continuous at every actual inverse
domain point. A common compact parameter neighborhood supplies the integral
majorant, with no condition away from the support. -/
theorem continuousAt_matrixKTransformDerivComplex
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ matrixKTransformDomain ν) :
    ContinuousAt (matrixKTransformDerivComplex ν α) S := by
  let U : Set (Matrix n n ℂ × selfAdjoint (Matrix n n ℂ)) :=
    {p | IsUnit (1 + p.1 * p.2.val)}
  have hU : IsOpen U := Units.isOpen.preimage
    (continuous_const.add (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨V,W,hVo,_hWo,hSV,hνW,hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := S)) hν hU
      (by rintro ⟨X,T⟩ ⟨rfl,hT⟩; exact hS.2 T hT)
  obtain ⟨C,hCc,hSC,hCV⟩ := exists_compact_subset (x := S) hVo (hSV (by simp))
  have hCU : C ×ˢ ν.support ⊆ U := fun p hp => hVW ⟨hCV hp.1,hνW hp.2⟩
  have hDc : ContinuousOn (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) =>
      matrixKResolventDerivComplex p.1 p.2.val) (C ×ˢ ν.support) := by
    intro p hp
    exact ((continuousAt_matrixKResolventDerivComplex p.1 p.2.val (hCU hp)).comp
      (f := fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (q.1,q.2.val))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt).continuousWithinAt
  have hI := (continuousOn_integral_of_continuousOn_compact_support ν hν hCc
    (F := fun X T => matrixKResolventDerivComplex X T.val) (by convert! hDc)).continuousAt
    (mem_interior_iff_mem_nhds.mp hSC)
  have hi := (hasFDerivAt_matrixInverse S hS.1).continuousAt
  have hleft := (ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)).continuous.continuousAt.comp hi
  have hInv := (hleft.clm_apply hi).const_smul α⁻¹
  exact hI.add hInv

/-- The actual K-transform is complex C1 near every point of its true
inverse domain. This supplies the differentiability input for the local
inverse theorem, rather than assuming an analytic branch exists. -/
theorem contDiffAt_matrixKTransform_complex
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ matrixKTransformDomain ν) :
    ContDiffAt ℂ 1 (matrixKTransform ν α) S := by
  refine contDiffAt_one_iff.mpr ⟨matrixKTransformDerivComplex ν α,
    matrixKTransformDomain ν, (isOpen_matrixKTransformDomain ν hν).mem_nhds hS,?_,?_⟩
  · intro X hX
    exact (continuousAt_matrixKTransformDerivComplex ν hν α hX).continuousWithinAt
  · intro X hX
    exact hasFDerivAt_matrixKTransform_complex ν hν α hX

end NLAlib
