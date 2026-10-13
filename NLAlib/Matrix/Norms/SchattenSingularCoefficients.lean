import NLAlib.Matrix.Norms.SchattenComparison
/-!
# Schatten norms of prescribed singular coefficients

Nonnegative decreasing coefficients in fixed orthogonal singular frames give
their exact power-sum norms and Frobenius pairings. These are the explicit
attainer ingredients for Schatten duality, Bhatia (1997), §IV.2.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Right multiplication by a matrix with orthonormal columns preserves the
Frobenius pairing when applied as its transpose.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem frobInner_mul_transpose_right_of_orthonormal {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]
    {V : Matrix n k ℝ} (hV : HasOrthonormalCols V) (A B : Matrix m k ℝ) :
    frobInner (A * Vᵀ) (B * Vᵀ) = frobInner A B := by
  rw [← frobInner_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, frobInner_mul_left_of_orthonormal (show Vᵀ * V = 1 from hV), frobInner_transpose]

/-- Pairing two rectangular diagonals is exactly the thin coordinate dot
product, including an empty diagonal.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem frobInner_rectDiag_rectDiag {m n : ℕ} (a b : ℕ → ℝ) :
    frobInner (rectDiag a : Matrix (Fin m) (Fin n) ℝ) (rectDiag b) =
      ∑ i ∈ Finset.range (min m n), a i * b i := by
  have hrows : frobInner (rectDiag a : Matrix (Fin m) (Fin n) ℝ) (rectDiag b) =
      ∑ i : Fin m, if i.val < n then a i * b i else 0 := by
    rw [frobInner_eq_sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < n
    · rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin n)]
      · simp [rectDiag_apply, hi]
      · intro j _ hj
        have hij : i.val ≠ j.val := fun he => hj (Fin.ext he.symm)
        simp [rectDiag_apply, hij]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hi]
      · intro j _
        have hij : i.val ≠ j.val := fun he => hi (he.symm ▸ j.isLt)
        simp [rectDiag_apply, hij]
  rw [hrows, Fin.sum_univ_eq_sum_range (fun i => if i < n then a i * b i else 0) m,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]

open scoped Matrix.Norms.L2Operator in
/-- Prescribed decreasing nonnegative singular coefficients have their exact
Schatten power norm in any fixed orthogonal frames.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem schattenNormReal_mul_rectDiag_mul_transpose {m n : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (b : ℕ → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b) (q : ℝ) :
    schattenNormReal (U * (rectDiag b : Matrix (Fin m) (Fin n) ℝ) * Vᵀ) q =
      (∑ i ∈ Finset.range (min m n), b i ^ q) ^ (1 / q) := by
  unfold schattenNormReal
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [singularValues_eq_of_eq_mul_rectDiag_mul
    (A := U * (rectDiag b : Matrix (Fin m) (Fin n) ℝ) * Vᵀ) (show Uᵀ * U = 1 from hU) (show Vᵀ * V = 1 from hV) hb0 hb rfl (Finset.mem_range.mp hi)]

/-- Pairing a matrix with prescribed coefficients in its own SVD frames gives
the exact singular-value dot product.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem IsSVD.frobInner_mul_rectDiag_mul_transpose {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {p q : ℕ}
    {A : Matrix m n ℝ} {U : Matrix m (Fin p) ℝ}
    {V : Matrix n (Fin q) ℝ} (h : IsSVD A U V) (b : ℕ → ℝ) :
    frobInner A (U * (rectDiag b : Matrix (Fin p) (Fin q) ℝ) * Vᵀ) =
      ∑ i ∈ Finset.range (min p q), singularValues A i * b i := by
  conv_lhs => rw [h.eq, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [frobInner_mul_transpose_right_of_orthonormal h.conjTranspose_mul_right,
    frobInner_mul_left_of_orthonormal h.conjTranspose_mul_left, frobInner_rectDiag_rectDiag]

end NLAlib
