import NLAlib.Matrix.Functions.PositiveConeRayleigh
import NLAlib.Matrix.Norms.HermitianFrobenius
import NLAlib.ForMathlib.Analysis.ConeRayleigh

/-!
# A PSD eigenvector at the Frobenius operator norm

Self-adjointness and preservation of the PSD cone imply that the
Frobenius Hilbert operator norm is attained as a nonnegative eigenvalue
on a nonzero PSD matrix. Hilbert-positive definiteness is not assumed.
Source: matrix_toolkit_open_routes_2026_10_15, F22.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A symmetric cone-positive operator on the Hermitian Frobenius space
has a nonzero PSD eigenmatrix at its operator norm. -/
theorem exists_posSemidef_norm_eigenvector
    (T : HermitianFrobenius ℂ n →L[ℝ] HermitianFrobenius ℂ n)
    (hT : T.IsSymmetric)
    (hpos : ∀ x, (hermitianFrobeniusMatrix ℂ n x).PosSemidef →
      (hermitianFrobeniusMatrix ℂ n (T x)).PosSemidef) :
    ∃ x, x ≠ 0 ∧ (hermitianFrobeniusMatrix ℂ n x).PosSemidef ∧ T x=‖T‖ • x := by
  let E := (hermitianFrobeniusEquiv ℂ n).symm.toLinearMap.comp
    (selfAdjointPart ℝ : Matrix n n ℂ →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
  let L := hermitianFrobeniusMatrixLinear.comp (T.toLinearMap.comp E)
  have hE (x : HermitianFrobenius ℂ n) : E (hermitianFrobeniusMatrix ℂ n x)=x := by
    apply (hermitianFrobeniusEquiv ℂ n).injective
    apply Subtype.ext
    change (selfAdjointPart ℝ (hermitianFrobeniusMatrix ℂ n x) : Matrix n n ℂ)=
      hermitianFrobeniusMatrix ℂ n x
    exact (isHermitian_hermitianFrobeniusMatrix x).isSelfAdjoint.coe_selfAdjointPart_apply ℝ
  have hL (x : HermitianFrobenius ℂ n) :
      L (hermitianFrobeniusMatrix ℂ n x)=hermitianFrobeniusMatrix ℂ n (T x) := by
    change hermitianFrobeniusMatrix ℂ n (T (E (hermitianFrobeniusMatrix ℂ n x)))=_
    rw [hE]
  have hLP (P : Matrix n n ℂ) (hP : P.PosSemidef) : (L P).PosSemidef := by
    have hh := hpos (toHermitianFrobenius hP.isHermitian) hP
    rwa [← hL, hermitianFrobeniusMatrix_toHermitianFrobenius] at hh
  apply T.exists_norm_eigenvector_of_rayleigh_majorants hT
    (fun x => (hermitianFrobeniusMatrix ℂ n x).PosSemidef)
  intro x
  obtain ⟨K,hK,hKn,hKQ⟩ := exists_posSemidef_rayleigh_majorant L hLP
    (isHermitian_hermitianFrobeniusMatrix x)
  let y := toHermitianFrobenius hK.isHermitian
  refine ⟨y,hK,?_,?_⟩
  · rw [norm_hermitianFrobenius, norm_hermitianFrobenius]
    change frobNorm K=frobNorm (hermitianFrobeniusMatrix ℂ n x)
    exact congrArg Real.sqrt hKn
  · have hLy : L K=hermitianFrobeniusMatrix ℂ n (T y) := hL y
    rw [hLy] at hKQ
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      inner_hermitianFrobenius, frobInner_comm, hL,
      hermitianFrobeniusMatrix_toHermitianFrobenius, y] using hKQ

end NLAlib
