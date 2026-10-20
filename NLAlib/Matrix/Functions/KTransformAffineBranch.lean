import NLAlib.Matrix.Functions.KTransformLocalRealBranch
import NLAlib.Matrix.Functions.KTransformPositiveDerivativeInverse

/-! # Actual affine-target inverse branches of the stable K transform

The genuine complex inverse theorem continues a stable real point in
every positive matrix target direction. Adjoint symmetry proves the
real branch property, and the native derivative inverse gives its sign.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- Every strictly positive target direction has an actual local stable
inverse branch through a genuine real K point. The branch is Hermitian
on real parameters and has strictly negative derivative. Neither real
branch existence nor a signed derivative is assumed.
Source: Montanari--Saeed (2026), Theorem 3, real order continuation.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_decreasing_affine_branch
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (S : M) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹+T.val).PosDef)
    (hpos : ∀ H : M, H.IsHermitian → H≠0 →
      0<frobInner H (matrixKTransformDeriv ν α S H))
    (H : M) (hH : H.PosDef) :
    ∃ (G : ℂ → M) (B : M), AnalyticAt ℂ G 0 ∧ G 0=S ∧ B.PosDef ∧
      HasDerivAt G (-B) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, (G t).IsHermitian) ∧
      ∀ᶠ z : ℂ in 𝓝 0, G z∈matrixKTransformDomain ν ∧
        matrixKTransform ν α (G z)=matrixKTransform ν α S-z•H := by
  obtain ⟨G, B, hGa, hG0, hGd, _hGR, _hBH, hDB, hGeq, hstable⟩ :=
    exists_analytic_real_matrixKTransform_affine_branch ν hν α hα S ⟨hS,hgap,hpos⟩
      (-H) hH.isHermitian.neg
  obtain ⟨C, hC, hDC⟩ := exists_posDef_matrixKTransformDeriv_preimage ν hν α hα
    S hS hgap hpos H hH
  have hDE (X : M) : matrixKTransformDerivComplex ν α S X = matrixKTransformDeriv ν α S X :=
    congrArg (fun L : M →L[ℝ] M => L X)
      (matrixKTransformDerivComplex_restrictScalars ν α S)
  have hB : matrixKTransformDerivComplex ν α S B = -H := by rw [hDE,hDB]
  have hCneg : matrixKTransformDerivComplex ν α S (-C) = -H := by rw [map_neg,hDE,hDC]
  have he : B = -C :=
    injective_matrixKTransformDerivComplex_of_quadratic_pos ν hν α hα S hS hgap hpos
      (hB.trans hCneg.symm)
  refine ⟨G,C,hGa,hG0,hC,?_,?_,?_⟩
  · simpa only [he] using hGd
  · exact hstable.mono fun _ ht => ht.1.isHermitian
  · simpa only [smul_neg,sub_eq_add_neg] using hGeq

end NLAlib
