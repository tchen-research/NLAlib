import NLAlib.Matrix.Functions.KTransformLocalInverse
import NLAlib.Matrix.Functions.KTransformNeumann

/-! # Native positive inverse of the stable K derivative

Whitening and the actual positive Neumann series construct the positive
preimage of each positive Hermitian direction. In particular the local
scalar inverse branch has a genuinely positive vertical slope.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- At an actual stable K point, every strictly positive matrix has a
strictly positive preimage under the native derivative. The preimage is
constructed by the convergent positive Neumann inverse of the true
Frobenius stability map.
Source: Montanari--Saeed (2026), Theorem 3, stable real-branch derivative.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_posDef_matrixKTransformDeriv_preimage
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (S : M) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hpos : ∀ H : M, H.IsHermitian → H≠0 →
      0<frobInner H (matrixKTransformDeriv ν α S H))
    (H : M) (hH : H.PosDef) :
    ∃ B : M, B.PosDef ∧ matrixKTransformDeriv ν α S B=H := by
  let Q := cfc Real.sqrt S
  let L := matrixKStabilityFrobenius ν hν α hα.le S hS hgap
  have hnorm : ‖L‖<1 :=
    (matrixKTransform_quadratic_iff_norm_lt_one ν hν α hα S hS hgap).mp hpos
  let C := α•(Q*H*Q)
  have hC : C.PosDef := ((posDef_sqrt_congruence_iff S hS H).mpr hH).smul hα
  let x := toHermitianFrobenius hC.isHermitian
  let Y := hermitianNeumannInverse L x
  let HY := hermitianFrobeniusMatrix ℂ n Y
  have hL : ∀ v : HermitianFrobenius ℂ n,
      (hermitianFrobeniusMatrix ℂ n v).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (L v)).PosSemidef :=
    posSemidef_matrixKStabilityFrobenius ν hν α hα.le S hS hgap
  have hY : HY.PosSemidef := posSemidef_hermitianNeumannInverse L hL hnorm hC.posSemidef
  have hLY : (hermitianFrobeniusMatrix ℂ n (L Y)).PosSemidef := hL Y hY
  have he := congrArg (hermitianFrobeniusMatrix ℂ n)
    (hermitianNeumannInverse_sub_map L hnorm x)
  have heq : HY-matrixKStabilityMap ν α S HY=C := by
    change HY-hermitianFrobeniusMatrix ℂ n (L Y)=C at he
    exact he
  have hHY : HY.PosDef := by
    have hd : HY=C+hermitianFrobeniusMatrix ℂ n (L Y) := by
      change HY-hermitianFrobeniusMatrix ℂ n (L Y)=C at he
      exact sub_eq_iff_eq_add.mp he
    rw [hd]
    exact hC.add_posSemidef hLY
  let B := Q*HY*Q
  refine ⟨B,(posDef_sqrt_congruence_iff S hS HY).mpr hHY,?_⟩
  rw [matrixKTransformDeriv_eq_congruence ν hν α hα.ne' S hS hgap B]
  change α⁻¹•(cfc (fun r => (Real.sqrt r)⁻¹) S *
    (cfc (fun r => (Real.sqrt r)⁻¹) S*(Q*HY*Q)*cfc (fun r => (Real.sqrt r)⁻¹) S-
      matrixKStabilityMap ν α S
        (cfc (fun r => (Real.sqrt r)⁻¹) S*(Q*HY*Q)*cfc (fun r => (Real.sqrt r)⁻¹) S))*
    cfc (fun r => (Real.sqrt r)⁻¹) S)=H
  rw [invSqrt_sqrt_congruence S hS HY,heq]
  change α⁻¹•(cfc (fun r => (Real.sqrt r)⁻¹) S *
    (α•(Q*H*Q))*cfc (fun r => (Real.sqrt r)⁻¹) S)=H
  rw [Matrix.mul_smul,Matrix.smul_mul,smul_smul,inv_mul_cancel₀ hα.ne',one_smul,
    invSqrt_sqrt_congruence S hS H]

/-- The local analytic scalar inverse at an actual stable real K point
has a strictly positive native derivative. The slope is obtained from
the true positive inverse of the K derivative, rather than assumed as a
branch property.
Source: Montanari--Saeed (2026), Theorem 3, real branch identification.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_inverse_branch_posDef_deriv
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (S : M) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hpos : ∀ H : M, H.IsHermitian → H≠0 →
      0<frobInner H (matrixKTransformDeriv ν α S H))
    (u : ℝ) (hK : matrixKTransform ν α S=(u : ℂ)•1) :
    ∃ (G : ℂ → M) (B : M), AnalyticAt ℂ G (u : ℂ) ∧ G u=S ∧ B.PosDef ∧
      HasDerivAt G B (u : ℂ) ∧
      ∀ᶠ z in 𝓝 (u : ℂ), G z∈matrixKTransformDomain ν ∧
        matrixKTransform ν α (G z)=z•1 := by
  obtain ⟨B,hB,hDB⟩ := exists_posDef_matrixKTransformDeriv_preimage ν hν α hα
    S hS hgap hpos 1 Matrix.PosDef.one
  obtain ⟨G,hGa,hG0,hGeq⟩ := exists_analytic_matrixKTransform_inverse_branch ν hν α hα
    S hS hgap hpos u hK
  let D := matrixKTransformDerivComplex ν α S
  have hD (X : M) : D X=matrixKTransformDeriv ν α S X :=
    congrArg (fun L : M →L[ℝ] M => L X)
      (matrixKTransformDerivComplex_restrictScalars ν α S)
  have hGd : HasDerivAt G (deriv G (u : ℂ)) (u : ℂ) := hGa.differentiableAt.hasDerivAt
  have hdom : S∈matrixKTransformDomain ν :=
    ⟨hS.isUnit,fun T hT => isUnit_matrixKDenominator S T.val hS (hgap T hT)⟩
  have hKd : HasFDerivAt (matrixKTransform ν α) D (G u) := by
    rw [hG0]
    exact hasFDerivAt_matrixKTransform_complex ν hν α hdom
  have hcomp := hKd.comp_hasDerivAt (u : ℂ) hGd
  have hEq : (fun z : ℂ => matrixKTransform ν α (G z))=ᶠ[𝓝 (u : ℂ)]
      (fun z : ℂ => z•(1 : M)) := hGeq.mono fun _ h => h.2
  have hscalar : HasDerivAt (fun z : ℂ => z•(1 : M)) 1 (u : ℂ) := by
    convert! (hasDerivAt_id (u : ℂ)).smul_const (1 : M) using 1
    simp only [one_smul]
  have hd : D (deriv G (u : ℂ))=1 := (hcomp.congr_of_eventuallyEq hEq.symm).unique hscalar
  have hderiv : deriv G (u : ℂ)=B :=
    injective_matrixKTransformDerivComplex_of_quadratic_pos ν hν α hα S hS hgap hpos
      (hd.trans ((hD B).trans hDB).symm)
  refine ⟨G,B,hGa,hG0,hB,?_,hGeq⟩
  rwa [hderiv] at hGd

end NLAlib
