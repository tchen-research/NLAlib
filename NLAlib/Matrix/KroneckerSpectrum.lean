import NLAlib.Matrix.KroneckerIdentities
import NLAlib.Matrix.PolynomialCalculus

/-!
# Eigenvalue multisets of Kronecker products and sums

Tensoring complete orthogonal diagonalizations identifies every eigenvalue with
its algebraic multiplicity. Pairwise lists are multisets: their lexicographic
order need not be the decreasing spectral order. Empty dimensions are included.
Source: Horn–Johnson 1991, Theorem 4.2.12. Atlas: `kronecker-spectral`.
-/

noncomputable section
open scoped Matrix Kronecker

namespace NLAlib

/-- An orthogonal diagonalization identifies the eigenvalue multiset, including
multiplicities and signed entries. The real spectral theorem; Kronecker helper.
-/
theorem multiset_eigenvalues_eq_of_orthogonal_diagonalization {n : Type*}
    [Fintype n] [DecidableEq n] {T P : Matrix n n ℝ} (hT : T.IsHermitian)
    (d : n → ℝ) (hP : Pᵀ * P = 1) (hTd : T = P * Matrix.diagonal d * Pᵀ) :
    Finset.univ.val.map hT.eigenvalues = Finset.univ.val.map d := by
  have hc : T.charpoly = (Matrix.diagonal d).charpoly := by
    rw [hTd, Matrix.charpoly_mul_comm]
    rw [← Matrix.mul_assoc Pᵀ P, hP, Matrix.one_mul]
  have hroots := hT.roots_charpoly_eq_eigenvalues
  rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod] at hroots
  · simpa using hroots.symm
  · exact Finset.prod_ne_zero_iff.mpr fun _ _ => Polynomial.X_sub_C_ne_zero _

/-- Tensor products of orthogonal matrices are orthogonal.
Horn–Johnson 1991, Theorem 4.2.15; all finite index types, including empty ones.
-/
theorem transpose_kronecker_mul_self_eq_one {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {U : Matrix m m ℝ} {V : Matrix n n ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    (U ⊗ₖ V)ᵀ * (U ⊗ₖ V) = 1 := by
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, hU, hV,
    Matrix.one_kronecker_one]

/-- Kronecker products of real symmetric matrices are symmetric.
Horn–Johnson 1991, Section 4.2, adjoint mixed-product identity.
-/
theorem isHermitian_kronecker {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

/-- Tensoring the two real orthogonal spectral decompositions diagonalizes the
Kronecker product with the pairwise eigenvalue products. Horn–Johnson 1991,
Theorem 4.2.12; the middle diagonal is not asserted to be sorted.
-/
theorem eq_eigenvectorUnitary_kronecker_mul_diagonal_mul_transpose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ⊗ₖ B =
      ((hA.eigenvectorUnitary : Matrix m m ℝ) ⊗ₖ (hB.eigenvectorUnitary : Matrix n n ℝ)) *
      Matrix.diagonal (fun ij => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) *
      ((hA.eigenvectorUnitary : Matrix m m ℝ) ⊗ₖ (hB.eigenvectorUnitary : Matrix n n ℝ))ᵀ := by
  conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA,
    eq_eigenvectorUnitary_mul_diagonal_mul_transpose hB]
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
    Matrix.diagonal_kronecker_diagonal, Matrix.kroneckerMap_transpose]

/-- The Kronecker product's eigenvalues are exactly all pairwise products, as a
multiset with algebraic multiplicities. Horn–Johnson 1991, Theorem 4.2.12.
Empty dimensions give empty multisets; pairwise products need sorting for an ordered list.
atlas: kronecker-spectral (partial) -/
theorem multiset_eigenvalues_kronecker {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Finset.univ.val.map (isHermitian_kronecker hA hB).eigenvalues =
      (Finset.univ : Finset (m × n)).val.map (fun ij => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) := by
  apply multiset_eigenvalues_eq_of_orthogonal_diagonalization _ _
    (transpose_kronecker_mul_self_eq_one (transpose_eigenvectorUnitary_mul_self hA)
      (transpose_eigenvectorUnitary_mul_self hB))
  exact eq_eigenvectorUnitary_kronecker_mul_diagonal_mul_transpose hA hB

/-- The Kronecker sum's eigenvalues are exactly all pairwise sums, as a multiset.
Horn–Johnson 1991, Theorem 4.2.12; signed symmetric spectra and empty types are included.
atlas: kronecker-spectral (partial) -/
theorem multiset_eigenvalues_kronecker_sum {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Finset.univ.val.map
      ((isHermitian_kronecker hA Matrix.isHermitian_one).add
        (isHermitian_kronecker Matrix.isHermitian_one hB)).eigenvalues =
      (Finset.univ : Finset (m × n)).val.map (fun ij => hA.eigenvalues ij.1 + hB.eigenvalues ij.2) := by
  let U : Matrix m m ℝ := hA.eigenvectorUnitary
  let V : Matrix n n ℝ := hB.eigenvectorUnitary
  have hU : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hA
  have hV : Vᵀ * V = 1 := transpose_eigenvectorUnitary_mul_self hB
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
  apply multiset_eigenvalues_eq_of_orthogonal_diagonalization _ _
    (transpose_kronecker_mul_self_eq_one hU hV)
  have hleft : A ⊗ₖ (1 : Matrix n n ℝ) = (U ⊗ₖ V) *
      Matrix.diagonal (fun ij => hA.eigenvalues ij.1) * (U ⊗ₖ V)ᵀ := by
    conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA, ← hV']
    rw [← Matrix.mul_one V, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.kroneckerMap_transpose]
    simp only [Matrix.mul_one]
    change ((U ⊗ₖ V) * (Matrix.diagonal hA.eigenvalues ⊗ₖ (1 : Matrix n n ℝ))) *
      (U ⊗ₖ V)ᵀ = _
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp only [mul_one]
  have hright : (1 : Matrix m m ℝ) ⊗ₖ B = (U ⊗ₖ V) *
      Matrix.diagonal (fun ij => hB.eigenvalues ij.2) * (U ⊗ₖ V)ᵀ := by
    conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hB, ← hU']
    rw [← Matrix.mul_one U, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.kroneckerMap_transpose]
    simp only [Matrix.mul_one]
    change ((U ⊗ₖ V) * ((1 : Matrix m m ℝ) ⊗ₖ Matrix.diagonal hB.eigenvalues)) *
      (U ⊗ₖ V)ᵀ = _
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp only [one_mul]
  rw [hleft, hright, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.diagonal_add]

end NLAlib
