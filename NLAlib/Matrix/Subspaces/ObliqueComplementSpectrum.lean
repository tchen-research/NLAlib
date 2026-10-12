import NLAlib.Matrix.Subspaces.ObliqueCanonicalSpectrum
/-!
# Singular values of the complementary oblique projection

Swapping the two coordinate blocks and transposing gives the same canonical
singular coefficients with the two block sizes exchanged. Horn–Johnson 2013,
Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The complementary oblique block matrix has the same nontrivial singular
values with the range/kernel sizes exchanged. This includes either empty block.
Horn–Johnson 2013, Corollary 3.4.3.3; supports `cs-decomposition`. -/
theorem singularValues_one_sub_oblique_canonical {r s : ℕ} (t : ℕ → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht : Antitone t)
    (hz : ∀ i, min r s ≤ i → t i = 0) (k : ℕ) :
    ((1 : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) -
      Matrix.fromBlocks 1 (rectDiag t) 0 0).toEuclideanLin.singularValues k =
      if k < s then Real.sqrt (1 + t k ^ 2) else 0 := by
  let L := (1 : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ) -
    Matrix.fromBlocks 1 (rectDiag t) 0 0
  let T : Matrix (Fin s) (Fin r) ℝ := rectDiag t
  let A := Matrix.fromBlocks (1 : Matrix (Fin s) (Fin s) ℝ) (-T) 0
    (0 : Matrix (Fin r) (Fin r) ℝ)
  let B := Matrix.fromBlocks (1 : Matrix (Fin s) (Fin s) ℝ) T 0
    (0 : Matrix (Fin r) (Fin r) ℝ)
  have hA : Lᵀ.reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _) = A := by
    ext i j
    cases i <;> cases j <;>
      simp [L, A, T, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.transpose_apply, Matrix.one_apply, rectDiag_apply, eq_comm]
    split_ifs with h <;> simp_all
  have hGram : A * Aᵀ = B * Bᵀ := by
    simp only [A, B, Matrix.fromBlocks_transpose, Matrix.transpose_one,
      Matrix.transpose_zero, Matrix.transpose_neg, Matrix.fromBlocks_multiply,
      Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.neg_mul, Matrix.mul_neg,
      neg_neg, neg_zero, add_zero]
  calc
    _ = A.toEuclideanLin.singularValues k := by
      rw [← singularValues_eq_linearMap, ← singularValues_eq_linearMap, ← hA, singularValues_reindex,
        singularValues_transpose]
    _ = B.toEuclideanLin.singularValues k := by
      rw [← singularValues_eq_linearMap, ← singularValues_eq_linearMap,
        ← singularValues_transpose A, ← singularValues_transpose B]
      apply toEuclideanLin_singularValues_eq_of_gram_eq
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hGram
    _ = _ := singularValues_oblique_canonical t ht0 ht (by simpa only [min_comm] using hz) k

end NLAlib
