import NLAlib.Matrix.Inequalities.HermitianPart
import NLAlib.Matrix.Inequalities.SchurHorn
import NLAlib.Matrix.Functions.RealComplexCFC
/-!
# Realizing eigenvalues and a prescribed Hermitian-part spectrum

The real Schur--Horn converse supplies a symmetric matrix with diagonal
`Re z`; doubling its strict upper triangle and inserting `z` on the diagonal
gives the required complex matrix. Source: Horn--Johnson (2013),
Theorem 4.3.50; atlas `real-part-eigenvalue-majorization`.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every real vector majorizing the real parts of a prescribed complex
eigenvalue list is realized as the Hermitian-part spectrum of a complex
matrix with exactly that eigenvalue list. Both characteristic polynomials
certify multiplicity; empty dimensions and repeated entries are included.
Horn--Johnson (2013), Theorem 4.3.50.
atlas: real-part-eigenvalue-majorization (partial) -/
theorem exists_matrix_charpoly_and_selfAdjointPart_charpoly_of_majorized
    (x : n → ℝ) (z : n → ℂ) (h : Majorized (fun i => (z i).re) x) :
    ∃ A : Matrix n n ℂ, A.charpoly = ∏ i, (X - C (z i)) ∧
      (selfAdjointPart ℝ A : Matrix n n ℂ).charpoly = ∏ i, (X - C (x i : ℂ)) := by
  classical
  obtain ⟨Q, hQ, hdiag⟩ := exists_orthogonal_diagonal_eq_of_majorized (fun i => (z i).re) x h
  let K := Q * diagonal x * Qᵀ
  have hKt : Kᵀ = K := by simp [K, Matrix.transpose_mul, Matrix.mul_assoc]
  have hKd (i : n) : K i i = (z i).re := congrFun hdiag i
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let T : Matrix n n ℂ := fun i j =>
    if i = j then z i else if e.symm i < e.symm j then 2 * (K i j : ℂ) else 0
  have hTd (i : n) : T i i = z i := by simp [T]
  have hTri : (T.submatrix e e).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    have hne : e i ≠ e j := fun he => (ne_of_gt hij) (e.injective he)
    simp [T, hne, not_lt.mpr hij.le]
  have hChar : T.charpoly = ∏ i, (X - C (z i)) := by
    calc
      T.charpoly = (T.submatrix e e).charpoly := (Matrix.charpoly_reindex e.symm T).symm
      _ = ∏ i : Fin (Fintype.card n), (X - C (z (e i))) := by
        rw [Matrix.charpoly_of_isUpperTriangular _ hTri]
        simp only [Matrix.submatrix_apply, hTd]
      _ = _ := e.prod_comp (fun i => X - C (z i))
  have hPart : (selfAdjointPart ℝ T : Matrix n n ℂ) = realMatrixComplexification K := by
    ext i j
    have hKji : K j i = K i j := congrArg (fun M : Matrix n n ℝ => M i j) hKt
    by_cases hij : i = j
    · subst j
      simp [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, T, hKd,
        realMatrixComplexification_apply, Complex.ext_iff, Complex.real_smul]
      ring
    · have hji : j ≠ i := Ne.symm hij
      by_cases hlt : e.symm i < e.symm j
      · have hnlt : ¬e.symm j < e.symm i := not_lt.mpr hlt.le
        simp [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, T, hij, hji,
          hlt, hnlt, realMatrixComplexification_apply, Complex.real_smul]
      · have hgt : e.symm j < e.symm i := lt_of_le_of_ne (le_of_not_gt hlt)
          (fun he => hij (e.symm.injective he.symm))
        simp [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, T, hij, hji,
          hlt, hgt, hKji, realMatrixComplexification_apply, Complex.real_smul]
  have hQc : (realMatrixComplexification Q)ᴴ * realMatrixComplexification Q = 1 := by
    have hQ' : star Q * Q = 1 := hQ
    rw [← Matrix.star_eq_conjTranspose, ← map_star, ← map_mul, hQ', map_one]
  have hKc : realMatrixComplexification K = realMatrixComplexification Q *
      diagonal (fun i => (x i : ℂ)) * (realMatrixComplexification Q)ᴴ := by
    have hmapT : realMatrixComplexification Qᵀ = (realMatrixComplexification Q)ᴴ := by
      rw [← Matrix.star_eq_conjTranspose, ← map_star]
      rfl
    have hmapD : realMatrixComplexification (diagonal x) = diagonal (fun i => (x i : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [realMatrixComplexification_apply, hij]
    dsimp only [K]
    rw [map_mul, map_mul, hmapT, hmapD]
  refine ⟨T, hChar, ?_⟩
  rw [hPart, hKc, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQc, Matrix.one_mul,
    Matrix.charpoly_diagonal]

end NLAlib
