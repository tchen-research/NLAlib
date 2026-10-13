import NLAlib.Matrix.Spectral.RealNormalForm
/-!
# Canonical blocks for real skew-symmetric and orthogonal matrices

The real normal form specializes to zero scalar blocks and pure skew planes,
or to scalar signs and planar rotations on the unit circle.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- In an orthogonal real normal form, isolated scalar blocks are `±1`,
and every nontrivial rotation block has coefficients on the unit circle.
Horn–Johnson 2013, Theorem 2.5.4; exact orthogonal specialization. -/
theorem real_normal_form_orthogonal_block_coefficients {k : ℕ}
    {T : Matrix (Fin k) (Fin k) ℝ} (hF : IsRealNormalForm T) (hT : HasOrthonormalCols T) :
    (∀ i, (∀ j, j ≠ i → T j i = 0) → T i i = -1 ∨ T i i = 1) ∧
    (∀ i j, j.val + 1 = i.val → T i j ≠ 0 → (T j j) ^ 2 + (T i j) ^ 2 = 1) := by
  have hN : T * Tᵀ = Tᵀ * T := (mul_eq_one_comm.mp hT).trans hT.symm
  have hcol (i : Fin k) : ∑ l, T l i * T l i = 1 := by
    have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M i i) (show Tᵀ * T = 1 from hT)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] using h
  constructor
  · intro i hi
    have hsum : ∑ l, T l i * T l i = T i i * T i i := by
      apply Finset.sum_eq_single i
      · intro l _ hli; rw [hi l hli, mul_zero]
      · simp
    have hs : (T i i) ^ 2 = 1 := by
      have h := hcol i
      rw [hsum] at h
      nlinarith [h]
    have hf : (T i i - 1) * (T i i + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · intro i j hij hn
    have hij' : i ≠ j := by intro h; subst i; omega
    have hsum : ∑ l, T l j * T l j = T j j * T j j + T i j * T i j := by
      calc
        _ = ∑ l, (if l = j then T j j * T j j else if l = i then T i j * T i j else 0) := by
          apply Finset.sum_congr rfl
          intro l _
          by_cases hlj : l = j
          · simp only [hlj, ite_true]
          by_cases hli : l = i
          · simp only [hli, hij', ite_false, ite_true]
          obtain ⟨_, hz⟩ := real_normal_quasi_row_eq_zero_of_pair hF.1.1 hN hij hn l hlj hli
          simp only [hlj, hli, ite_false, hz, mul_zero]
        _ = _ := by
          have hfilter : Finset.univ.filter (fun l : Fin k => l = j) = {j} := by
            ext l; simp
          simp [Finset.sum_ite, hij', hfilter]
    have h := hcol j
    rw [hsum] at h
    nlinarith [h]

/-- Every real skew-symmetric matrix is orthogonally similar to a direct
sum of zero scalar blocks and blocks `[[0,b],[-b,0]]`. The exact zero
diagonal is supplied in addition to the real normal block structure.
Horn–Johnson 2013, Theorem 2.5.4.
atlas: normal-matrices (partial) -/
theorem exists_orthogonal_real_skew_normal_form {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Aᵀ = -A) (order : Fin (Fintype.card n) ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᵀ ∧
      IsRealNormalForm (T.submatrix order order) ∧ ∀ i, T i i = 0 := by
  have hN : A * Aᵀ = Aᵀ * A := by rw [hA, Matrix.mul_neg, Matrix.neg_mul]
  obtain ⟨Q, T, hQ, hAT, hF⟩ := exists_orthogonal_real_normal_form A hN order
  have hconj : Qᵀ * A * Q = T := by
    rw [hAT]
    calc
      _ = (Qᵀ * Q) * T * (Qᵀ * Q) := by simp only [Matrix.mul_assoc]
      _ = T := by rw [(show Qᵀ * Q = 1 from hQ), Matrix.one_mul, Matrix.mul_one]
  have hskew : Tᵀ = -T := by
    rw [← hconj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  refine ⟨Q, T, hQ, hAT, hF, fun i => ?_⟩
  have h := congrArg (fun M : Matrix n n ℝ => M i i) hskew
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  linarith

/-- Every real orthogonal matrix is orthogonally similar to a direct sum
of scalar signs `±1` and planar rotations `[[a,b],[-b,a]]` with
`a²+b²=1`. The block pattern, scalar signs and circle equation are supplied
explicitly, including empty dimension. Horn–Johnson 2013, Theorem 2.5.4.
atlas: normal-matrices (partial) -/
theorem exists_orthogonal_real_orthogonal_normal_form {n : Type*}
    [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : HasOrthonormalCols A)
    (order : Fin (Fintype.card n) ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᵀ ∧
      IsRealNormalForm (T.submatrix order order) ∧
      (∀ i, (∀ j, j ≠ i → T (order j) (order i) = 0) →
        T (order i) (order i) = -1 ∨ T (order i) (order i) = 1) ∧
      (∀ i j, j.val + 1 = i.val → T (order i) (order j) ≠ 0 →
        (T (order j) (order j)) ^ 2 + (T (order i) (order j)) ^ 2 = 1) := by
  have hN : A * Aᵀ = Aᵀ * A := (mul_eq_one_comm.mp hA).trans hA.symm
  obtain ⟨Q, T, hQ, hAT, hF⟩ := exists_orthogonal_real_normal_form A hN order
  have hconj : Qᵀ * A * Q = T := by
    rw [hAT]
    calc
      _ = (Qᵀ * Q) * T * (Qᵀ * Q) := by simp only [Matrix.mul_assoc]
      _ = T := by rw [(show Qᵀ * Q = 1 from hQ), Matrix.one_mul, Matrix.mul_one]
  have hT : HasOrthonormalCols T := by
    rw [← hconj]
    exact (hQ.transpose.mul hA).mul hQ
  have hTe : HasOrthonormalCols (T.submatrix order order) := by
    change Tᵀ.submatrix order order * T.submatrix order order = 1
    rw [Matrix.submatrix_mul_equiv, (show Tᵀ * T = 1 from hT)]
    ext i j
    simp [Matrix.one_apply, order.injective.eq_iff]
  obtain ⟨hscalar, hrotation⟩ := real_normal_form_orthogonal_block_coefficients hF hTe
  exact ⟨Q, T, hQ, hAT, hF, hscalar, hrotation⟩

end NLAlib
