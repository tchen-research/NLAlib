import NLAlib.Matrix.Inequalities.TraceTail
/-!
# Determinant bounds for orthogonal compressions

Multiplying the interlacing inequalities gives the top-eigenvalue determinant
bound, including the zero-dimensional determinant `1`.
Source: Horn–Johnson 2013, Poincaré separation; the Horn product proof in
`matrix_toolkit_remaining_operator_derivations.tex`, Section 4.
Supports `horn-product-inequality`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Products over the matrix-labelled and sorted eigenvalue lists agree.
Mathlib's spectral ordering convention; supports Horn's product inequality.
-/
theorem prod_eigenvalues_eq_prod_sorted {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (∏ i : n, f (hA.eigenvalues i)) = ∏ i : Fin (Fintype.card n), f (hA.eigenvalues₀ i) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [← e.prod_comp (fun i : n => f (hA.eigenvalues i))]
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]

/-- The determinant of a positive semidefinite orthogonal compression is at most
the product of the corresponding top eigenvalues. Poincaré separation,
Horn–Johnson 2013, Corollary 4.3.37. The empty compression has determinant `1`.
-/
theorem det_transpose_mul_mul_le_prod_eigenvalues₀ {n r : Type*}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    {G : Matrix n n ℝ} (hG : G.PosSemidef) {Q : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) :
    (Qᵀ * G * Q).det ≤ ∏ i : Fin (Fintype.card r),
      hG.isHermitian.eigenvalues₀ (Fin.castLE (card_le_card_of_hasOrthonormalCols hQ) i) := by
  have hC : (Qᵀ * G * Q).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      Matrix.mul_assoc] using hG.mul_mul_conjTranspose_same Qᵀ
  have hd : (Qᵀ * G * Q).det = ∏ i : Fin (Fintype.card r), hC.isHermitian.eigenvalues₀ i := by
    calc
      _ = ∏ i : r, hC.isHermitian.eigenvalues i := by
        simpa using hC.isHermitian.det_eq_prod_eigenvalues
      _ = _ := prod_eigenvalues_eq_prod_sorted hC.isHermitian (fun x => x)
  rw [hd]
  apply Finset.prod_le_prod
  · intro i _
    exact eigenvalues₀_nonneg_of_posSemidef hC i
  · intro i _
    exact Matrix.IsHermitian.eigenvalues₀_compression_le hG.isHermitian hQ hC.isHermitian i

/-- The Gram determinant of the image of an orthonormal frame is bounded by the
product of the squared top singular values. Horn–Johnson 1991, Theorem 3.3.4,
compression-determinant step; all empty and rank deficient cases are included.
-/
theorem det_gram_mul_le_prod_sq_singularValues {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {Q : Matrix (Fin n) (Fin k) ℝ}
    (hQ : HasOrthonormalCols Q) :
    ((A * Q)ᵀ * (A * Q)).det ≤ ∏ i : Fin k, singularValues A i ^ 2 := by
  have hG : (Aᵀ * A).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  have h := det_transpose_mul_mul_le_prod_eigenvalues₀ hG hQ
  have hkn : k ≤ n := by simpa using card_le_card_of_hasOrthonormalCols hQ
  rw [Matrix.transpose_mul]
  rw [show (Qᵀ * Aᵀ) * (A * Q) = Qᵀ * (Aᵀ * A) * Q by simp only [Matrix.mul_assoc]]
  refine h.trans_eq ?_
  rw [← (finCongr (Fintype.card_fin k).symm).prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  have hi : singularValues A (Fin.castLE hkn i) ^ 2 =
      hG.isHermitian.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm (Fin.castLE hkn i)) :=
    sq_singularValues_eq_eigenvalues₀ A (Fin.cast (Fintype.card_fin n).symm (Fin.castLE hkn i))
  simpa only [Fin.val_castLE, Fin.val_cast, Fin.castLE, Fin.cast, finCongr_apply] using hi.symm

end NLAlib
