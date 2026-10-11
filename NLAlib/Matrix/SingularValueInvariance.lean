import NLAlib.Matrix.KyFanFiniteIndex

/-!
# Native finite-index singular-value invariances

Successive Ky Fan prefixes recover every individual singular value. Their norm
invariances therefore provide the native linear-map APIs at arbitrary finite
matrix indices. Source: Horn–Johnson (2013), §2.6.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Native singular values are absolutely homogeneous on arbitrary finite indices. -/
theorem toEuclideanLin_singularValues_smul (A : Matrix m n ℝ) (c : ℝ) (k : ℕ) :
    (c • A).toEuclideanLin.singularValues k = |c| * A.toEuclideanLin.singularValues k := by
  have h1 := kyFanNorm_smul A c k
  have h2 := kyFanNorm_smul A c (k + 1)
  simp only [kyFanNorm, Finset.sum_range_succ] at h1 h2
  rw [h1] at h2
  nlinarith

/-- Native singular values are invariant under left orthogonal multiplication. -/
theorem toEuclideanLin_singularValues_orthogonal_mul (A : Matrix m n ℝ)
    {U : Matrix m m ℝ} (hU : HasOrthonormalCols U) (k : ℕ) :
    (U * A).toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  have h1 := kyFanNorm_orthogonal_mul A hU k
  have h2 := kyFanNorm_orthogonal_mul A hU (k + 1)
  simp only [kyFanNorm, Finset.sum_range_succ] at h1 h2
  rw [h1] at h2
  linarith

omit [DecidableEq m] in
/-- Native singular values are invariant under right orthogonal multiplication. -/
theorem toEuclideanLin_singularValues_mul_orthogonal (A : Matrix m n ℝ)
    {V : Matrix n n ℝ} (hV : HasOrthonormalCols V) (k : ℕ) :
    (A * V).toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  have h1 := kyFanNorm_mul_orthogonal A hV k
  have h2 := kyFanNorm_mul_orthogonal A hV (k + 1)
  simp only [kyFanNorm, Finset.sum_range_succ] at h1 h2
  rw [h1] at h2
  linarith

/-- Transposition preserves every native singular value, including padded zeros. -/
theorem toEuclideanLin_singularValues_transpose (A : Matrix m n ℝ) (k : ℕ) :
    Aᵀ.toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  have h1 := kyFanNorm_transpose A k
  have h2 := kyFanNorm_transpose A (k + 1)
  simp only [kyFanNorm, Finset.sum_range_succ] at h1 h2
  rw [h1] at h2
  linarith

end NLAlib
