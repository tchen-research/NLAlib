import NLAlib.Matrix.Spectral.RealNormalBlocks
import NLAlib.Matrix.Spectral.RealSchurSimilarity
/-!
# Scalar and rotation-dilation blocks for real normal matrices

Normality removes every cross-block entry of real Schur form. Its remaining
two-dimensional blocks have opposite off-diagonal entries, hence are exactly
rotation-dilation blocks, with no assumption on dimension or multiplicities.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- A real normal form has the real Schur block pattern and opposite
off-diagonal entries. Thus it is a direct sum of real scalar blocks and
blocks `[[a,b],[-b,a]]` with `b≠0`. Horn–Johnson 2013, Theorem 2.5.4. -/
def IsRealNormalForm {k : ℕ} (T : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsRealSchurForm T ∧ ∀ i j, i ≠ j → T i j = -T j i

/-- A nonzero two-dimensional block of a real normal quasitriangular
matrix has no other entries in its first row or column.
Horn–Johnson 2013, Lemma 2.5.2; real normal form helper. -/
theorem real_normal_quasi_row_eq_zero_of_pair {k : ℕ}
    {T : Matrix (Fin k) (Fin k) ℝ} (hT : IsUpperQuasiTriangular T)
    (hN : T * Tᵀ = Tᵀ * T) {i j : Fin k} (hij : i.val + 1 = j.val)
    (hji : T j i ≠ 0) (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
    T i l = 0 ∧ T l i = 0 := by
  by_cases hleft : l.val + 1 < i.val
  · exact ⟨hT.1 i l hleft, real_normal_quasi_eq_zero_above_superdiagonal hT hN l i hleft⟩
  by_cases hright : i.val + 1 < l.val
  · exact ⟨real_normal_quasi_eq_zero_above_superdiagonal hT hN i l hright, hT.1 l i hright⟩
  have hli' : l.val + 1 = i.val := by
    have := Fin.val_ne_of_ne hli
    have := Fin.val_ne_of_ne hlj
    omega
  have hz : T i l = 0 := (hT.2 j i l hij hli').resolve_left hji
  exact ⟨hz, real_normal_quasi_eq_zero_of_subdiagonal_eq_zero hT hN hli' hz⟩

/-- A real normal matrix already in corrected real Schur form has opposite
off-diagonal entries. Hence the nonscalar blocks are rotation-dilations.
Horn–Johnson 2013, Theorem 2.5.4; includes scalar and empty forms. -/
theorem isRealNormalForm_of_isRealSchurForm {k : ℕ}
    {T : Matrix (Fin k) (Fin k) ℝ} (hT : IsRealSchurForm T)
    (hN : T * Tᵀ = Tᵀ * T) : IsRealNormalForm T := by
  have hupper : ∀ i j : Fin k, i < j → T i j = -T j i := by
    intro i j hij
    by_cases hfar : i.val + 1 < j.val
    · rw [real_normal_quasi_eq_zero_above_superdiagonal hT.1 hN i j hfar,
        hT.1.1 j i hfar, neg_zero]
    have hadj : i.val + 1 = j.val := by omega
    by_cases hji : T j i = 0
    · rw [real_normal_quasi_eq_zero_of_subdiagonal_eq_zero hT.1 hN hadj hji, hji, neg_zero]
    have hdiag := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M i i) hN
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hdiag
    have hsum : ∑ l, (T i l * T i l - T l i * T l i) = 0 := by
      rw [Finset.sum_sub_distrib, hdiag, sub_self]
    have hsingle : ∑ l, (T i l * T i l - T l i * T l i) =
        T i j * T i j - T j i * T j i := by
      apply Finset.sum_eq_single j
      · intro l _ hlj
        by_cases hli : l = i
        · simp only [hli, sub_self]
        · obtain ⟨h₁, h₂⟩ := real_normal_quasi_row_eq_zero_of_pair hT.1 hN hadj hji l hli hlj
          rw [h₁, h₂, mul_zero, sub_self]
      · simp
    have hsquares : (T i j) ^ 2 = (T j i) ^ 2 := by
      rw [hsingle] at hsum
      nlinarith [hsum]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares with heq | heq
    · have hneg := (hT.2 j i hadj hji).2
      rw [heq] at hneg
      nlinarith [sq_nonneg (T j i)]
    · exact heq
  refine ⟨hT, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact hupper i j h
  · have h' := hupper j i h
    linarith

/-- Orthogonal similarity preserves real normality. Horn–Johnson 2013,
Section 2.5; real normal canonical form helper. -/
theorem real_normal_orthogonal_conjugate {n : Type*} [Fintype n] [DecidableEq n]
    {A Q : Matrix n n ℝ} (hA : A * Aᵀ = Aᵀ * A) (hQ : HasOrthonormalCols Q) :
    (Qᵀ * A * Q) * (Qᵀ * A * Q)ᵀ = (Qᵀ * A * Q)ᵀ * (Qᵀ * A * Q) := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = Qᵀ * (A * Aᵀ) * Q := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᵀ, hQQ, Matrix.one_mul]
    _ = Qᵀ * (Aᵀ * A) * Q := by rw [hA]
    _ = _ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᵀ, hQQ, Matrix.one_mul]

/-- Every real normal matrix is orthogonally similar to a direct sum of
scalar blocks and real rotation-dilation blocks `[[a,b],[-b,a]]`.
The block pattern and all coefficients are recorded by `IsRealNormalForm`
in any supplied enumeration of finite labels; dimension zero is included.
Horn–Johnson 2013, Theorem 2.5.4.
atlas: normal-matrices (partial) -/
theorem exists_orthogonal_real_normal_form {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A * Aᵀ = Aᵀ * A) (order : Fin (Fintype.card n) ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᵀ ∧
      IsRealNormalForm (T.submatrix order order) := by
  obtain ⟨Q, T, hQ, hAT, hT⟩ := exists_orthogonal_real_schur A order
  have hconj : Qᵀ * A * Q = T := by
    rw [hAT]
    calc
      _ = (Qᵀ * Q) * T * (Qᵀ * Q) := by simp only [Matrix.mul_assoc]
      _ = T := by rw [hQ, Matrix.one_mul, Matrix.mul_one]
  have hN : T * Tᵀ = Tᵀ * T := by
    simpa only [hconj] using real_normal_orthogonal_conjugate hA hQ
  refine ⟨Q, T, hQ, hAT, isRealNormalForm_of_isRealSchurForm hT ?_⟩
  simp only [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hN]

end NLAlib
