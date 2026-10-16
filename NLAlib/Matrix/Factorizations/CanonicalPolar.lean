import NLAlib.Matrix.Spectral.ThinSingularFunctions
import NLAlib.Matrix.Basic.MoorePenroseRank
import NLAlib.Matrix.Basic.MoorePenroseTransformations
import NLAlib.ForMathlib.LinearAlgebra.Matrix.RankInvertibility
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # The canonical partial polar factor over the complex numbers

The formula uses the Moore–Penrose inverse of the positive Gram square root,
so it is defined at arbitrary rank and annihilates the zero singular directions.
At full column rank the Moore–Penrose inverse is the ordinary inverse.
Source: Horn–Johnson, §7.3; Higham (1986), §3.2.
-/
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- The canonical partial polar factor, defined also for rank-deficient matrices. -/
def canonicalPartialPolar (A : Matrix m n ℂ) : Matrix m n ℂ :=
  A * moorePenroseInverse (CFC.sqrt (Aᴴ * A))

omit [DecidableEq m] in
/-- The positive Gram square root in any thin SVD, including the empty block. -/
theorem IsThinSVD.sqrt_gram_eq {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ) :
    CFC.sqrt (Aᴴ * A) = thinSingularMatrix V V σ := by
  have hD : (Matrix.diagonal fun i => (σ i : ℂ)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => by
      exact_mod_cast (h.pos i).le)
  have hS : (thinSingularMatrix V V σ).PosSemidef :=
    hD.mul_mul_conjTranspose_same V
  apply CFC.sqrt_unique _ hS.nonneg
  change thinSingularMatrix V V σ * thinSingularMatrix V V σ = Aᴴ * A
  rw [thinSingularMatrix_mul V V V h.right_orth]
  rw [h.eq]
  change thinSingularMatrix V V (fun i => σ i * σ i) =
    (thinSingularMatrix U V σ)ᴴ * thinSingularMatrix U V σ
  rw [thinSingularMatrix_gram U V h.left_orth]
  simp only [pow_two]

omit [DecidableEq m] in
/-- Every thin SVD identifies the same canonical partial polar factor.
Zero singular directions contribute zero automatically.
Source: Horn–Johnson, §7.3. -/
theorem IsThinSVD.canonicalPartialPolar_eq {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ) :
    canonicalPartialPolar A = U * Vᴴ := by
  have hS : IsThinSVD (CFC.sqrt (Aᴴ * A)) V V σ :=
    ⟨h.right_orth, h.right_orth, h.pos, h.sqrt_gram_eq⟩
  rw [canonicalPartialPolar, hS.moorePenroseInverse_eq, h.eq]
  simp only [← RCLike.ofReal_inv]
  change thinSingularMatrix U V σ * thinSingularMatrix V V (fun i => (σ i)⁻¹) = _
  rw [thinSingularMatrix_mul U V V h.right_orth]
  have hc : (fun i => σ i * (σ i)⁻¹) = (fun _ : r => (1 : ℝ)) := by
    funext i
    exact mul_inv_cancel₀ (h.pos i).ne'
  rw [hc]
  simp [thinSingularMatrix]

omit [DecidableEq m] in
/-- The canonical partial polar factor is exactly the inverse-square-root
formula when the column Gram matrix is nonsingular. -/
theorem canonicalPartialPolar_eq_mul_inv_sqrt {A : Matrix m n ℂ}
    (hA : IsUnit (Aᴴ * A)) :
    canonicalPartialPolar A = A * (CFC.sqrt (Aᴴ * A))⁻¹ := by
  rw [canonicalPartialPolar, moorePenroseInverse_eq_inv_of_isUnit _
    ((CFC.isUnit_sqrt_iff _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg).mpr hA)]

omit [DecidableEq m] in
/-- Full column rank gives a nonsingular column Gram matrix over the complex numbers. -/
theorem isUnit_gram_of_rank_eq_card {A : Matrix m n ℂ}
    (hA : A.rank = Fintype.card n) : IsUnit (Aᴴ * A) := by
  apply Matrix.isUnit_of_rank_eq_card
  rwa [Matrix.rank_conjTranspose_mul_self]

omit [DecidableEq m] in
/-- A full-column-rank thin SVD has a complete right singular frame. -/
theorem IsThinSVD.right_mul_conjTranspose_eq_one_of_rank_eq_card
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (hA : A.rank = Fintype.card n) : V * Vᴴ = 1 := by
  rw [← h.moorePenroseInverse_mul_eq,
    moorePenroseInverse_eq_pinvL A (isUnit_gram_of_rank_eq_card hA),
    pinvL_mul (isUnit_gram_of_rank_eq_card hA)]

omit [DecidableEq m] in
/-- At full column rank the canonical partial polar factor is a column isometry.
This is the target of the rectangular polar iterations. -/
theorem hasOrthonormalCols_canonicalPartialPolar_of_rank_eq_card {A : Matrix m n ℂ}
    (hA : A.rank = Fintype.card n) : HasOrthonormalCols (canonicalPartialPolar A) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  have hGram := isUnit_gram_of_rank_eq_card hA
  rw [h.canonicalPartialPolar_eq, hasOrthonormalCols_iff_conjTranspose_mul_self,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ U Vᴴ, h.left_orth.conjTranspose_mul_self, Matrix.one_mul]
  rw [← h.moorePenroseInverse_mul_eq, moorePenroseInverse_eq_pinvL A hGram, pinvL_mul hGram]

end NLAlib
