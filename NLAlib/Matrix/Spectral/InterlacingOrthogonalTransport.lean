import NLAlib.Matrix.Spectral.OrderedSymmetricDiagonalization
/-!
# Orthogonal transport of converse-interlacing constructions

The leading block is preserved under a block orthogonal conjugation, and
rank-one updates carry their coupling vector through the same orthogonal
change of coordinates. Source: Horn–Johnson (2013), converse interlacing.
-/
noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Orthogonal conjugation preserves the characteristic polynomial.
Source: similarity invariance, used by the converse-interlacing transports. -/
theorem charpoly_mul_mul_transpose_of_hasOrthonormalCols
    (Q A : Matrix n n ℝ) (hQ : HasOrthonormalCols Q) :
    (Q * A * Qᵀ).charpoly = A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, (show Qᵀ * Q = 1 from hQ), Matrix.one_mul]

omit [DecidableEq n] in
/-- Orthogonal conjugation transports a symmetric rank-one update by
applying the orthogonal factor to the coupling vector.
Horn–Johnson (2013), converse-interlacing transport. -/
theorem mul_add_vecMulVec_mul_transpose (Q A : Matrix n n ℝ) (v : n → ℝ) :
    Q * (A + Matrix.vecMulVec v v) * Qᵀ =
      Q * A * Qᵀ + Matrix.vecMulVec (Q *ᵥ v) (Q *ᵥ v) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose]

omit [DecidableEq n] in
/-- Applying the block orthogonal factor `diag(Q,1)` to an arrowhead
preserves its border scalar and carries its coupling vector to `Qv`.
Source: Horn–Johnson (2013), converse interlacing; this algebraic identity
does not require orthogonality. -/
theorem fromBlocks_mul_arrowhead_mul_transpose
    (Q A : Matrix n n ℝ) (v : n → ℝ) (a : ℝ) :
    let P : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) ℝ := Matrix.fromBlocks Q 0 0 1
    P * Matrix.fromBlocks A (Matrix.replicateCol (Fin 1) v)
      (Matrix.replicateRow (Fin 1) v) (Matrix.of fun _ _ : Fin 1 => a) * Pᵀ =
      Matrix.fromBlocks (Q * A * Qᵀ) (Matrix.replicateCol (Fin 1) (Q *ᵥ v))
        (Matrix.replicateRow (Fin 1) (Q *ᵥ v)) (Matrix.of fun _ _ : Fin 1 => a) := by
  dsimp only
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext i j
  simp only [Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, mul_comm]

/-- An arrowhead constructed over a diagonal list transports to any real
symmetric matrix with that full characteristic-root list.
Horn–Johnson (2013), converse interlacing; the border scalar is unchanged
and the equality is of complete characteristic polynomials. -/
theorem exists_bordered_charpoly_of_diagonal_construction
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (d v : n → ℝ) (a : ℝ)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    ∃ u : n → ℝ,
      (Matrix.fromBlocks A (Matrix.replicateCol (Fin 1) u)
        (Matrix.replicateRow (Fin 1) u) (Matrix.of fun _ _ : Fin 1 => a)).charpoly =
      (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol (Fin 1) v)
        (Matrix.replicateRow (Fin 1) v) (Matrix.of fun _ _ : Fin 1 => a)).charpoly := by
  obtain ⟨Q, hQ, hdiag⟩ := exists_orthogonal_diagonalization_of_isHermitian_with_charpoly A hA d hd
  refine ⟨Q *ᵥ v, ?_⟩
  let P : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) ℝ := Matrix.fromBlocks Q 0 0 1
  change Qᵀ * Q = 1 at hQ
  have hP : HasOrthonormalCols P := by
    rw [hasOrthonormalCols_iff_conjTranspose_mul_self,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    dsimp only [P]
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.one_mul, hQ, Matrix.fromBlocks_one]
  rw [hdiag, ← fromBlocks_mul_arrowhead_mul_transpose]
  exact charpoly_mul_mul_transpose_of_hasOrthonormalCols P _ hP

/-- A positive rank-one update over a diagonal list transports to any
real symmetric matrix with that full characteristic-root list.
Source: Horn–Johnson (2013), converse interlacing; the entire characteristic
polynomial, including multiplicities, is preserved. -/
theorem exists_add_vecMulVec_charpoly_of_diagonal_construction
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (d v : n → ℝ)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    ∃ u : n → ℝ, (A + Matrix.vecMulVec u u).charpoly =
      (Matrix.diagonal d + Matrix.vecMulVec v v).charpoly := by
  obtain ⟨Q, hQ, hdiag⟩ := exists_orthogonal_diagonalization_of_isHermitian_with_charpoly A hA d hd
  refine ⟨Q *ᵥ v, ?_⟩
  rw [hdiag, ← mul_add_vecMulVec_mul_transpose]
  exact charpoly_mul_mul_transpose_of_hasOrthonormalCols Q _ hQ

/-- Negating a real symmetric matrix negates every entry of any complete
characteristic-root list, including multiplicities. Source: the spectral
theorem; helper for the negative rank-one converse-interlacing construction. -/
theorem charpoly_neg_eq_prod_of_isHermitian
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (d : n → ℝ)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    (-A).charpoly = ∏ i, (X - C (-d i)) := by
  obtain ⟨Q, hQ, hdiag⟩ := exists_orthogonal_diagonalization_of_isHermitian_with_charpoly A hA d hd
  have hneg : -A = Q * Matrix.diagonal (fun i => -d i) * Qᵀ := by
    rw [← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul, hdiag]
  rw [hneg, charpoly_mul_mul_transpose_of_hasOrthonormalCols Q _ hQ, Matrix.charpoly_diagonal]

end NLAlib
