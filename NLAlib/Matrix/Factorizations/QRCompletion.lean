import NLAlib.Matrix.Factorizations.QRExistence
/-!
# Full QR and its triangular corner

Extend a thin QR frame to an ambient orthogonal matrix. The rectangular
full factor has the thin upper-triangular factor in the chosen coordinate
corner and zero rows elsewhere. Source: Trefethen--Bau, Theorem 7.1;
Golub--Van Loan, Theorem 5.2.1. Atlas: `qr-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Every thin QR extends to a full QR with the same triangular
factor in the specified coordinate corner and zero rows outside it. The
orthogonal completion agrees with the supplied frame in its chosen columns.
Trefethen--Bau, Theorem 7.1; supports `qr-decomposition`. -/
theorem exists_full_qr_completion {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) (e : n ↪ m) :
    ∃ W : Matrix m m ℝ, ∃ T : Matrix m n ℝ,
      HasOrthonormalCols W ∧ W.submatrix id e = Q ∧
        W * T = A ∧ T.submatrix e id = R ∧ (∀ i ∉ Set.range e, ∀ j, T i j = 0) := by
  let J : Matrix m n ℝ := (1 : Matrix m m ℝ).submatrix id e
  have hJ : HasOrthonormalCols J := by
    have hOne : HasOrthonormalCols (1 : Matrix m m ℝ) := by simp [HasOrthonormalCols]
    exact hOne.submatrix_cols e
  have hGram : Qᵀ * Q = Jᵀ * J := (show Qᵀ * Q = 1 from hQ).trans hJ.symm
  obtain ⟨W, hW, hWQ⟩ := exists_orthogonal_mul_eq_of_gram_eq Q J hGram
  refine ⟨W, J * R, hW, ?_, ?_, ?_, ?_⟩
  · change W * (1 : Matrix m m ℝ).submatrix (Equiv.refl m) e = Q at hWQ
    rw [Matrix.mul_submatrix_one] at hWQ
    exact hWQ
  · rw [← Matrix.mul_assoc, hWQ, hFactor]
  · ext i j
    simp [J, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.one_apply, e.injective.eq_iff]
  · intro i hi j
    have hNe (k : n) : i ≠ e k := by
      intro h
      exact hi ⟨k, h.symm⟩
    simp [J, Matrix.mul_apply, hNe]

/-- Full QR over arbitrary finite indices with the triangular corner located
by a specified column embedding. All rows outside the corner vanish, so this
is a full factorization, including singular and empty inputs.
Trefethen--Bau, Theorem 7.1; Golub--Van Loan, Theorem 5.2.1.
atlas: qr-decomposition (partial) -/
theorem exists_full_qr_of_embedding {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [LinearOrder n] (A : Matrix m n ℝ) (e : n ↪ m) :
    ∃ W : Matrix m m ℝ, ∃ R : Matrix n n ℝ, ∃ T : Matrix m n ℝ,
      HasOrthonormalCols W ∧ R.IsUpperTriangular ∧ (∀ i, 0 ≤ R i i) ∧
        W * T = A ∧ T.submatrix e id = R ∧ (∀ i ∉ Set.range e, ∀ j, T i j = 0) := by
  obtain ⟨Q, R, ⟨hFactor, hQ, hUpper⟩, hDiag⟩ :=
    exists_isQR A (Fintype.card_le_of_injective e e.injective)
  replace hFactor := hFactor.symm
  obtain ⟨W, T, hW, _, hFullFactor, hCorner, hZero⟩ := exists_full_qr_completion hQ hFactor e
  exact ⟨W, R, T, hW, hUpper, hDiag, hFullFactor, hCorner, hZero⟩

/-- For standard finite coordinates, full QR has its nonnegative
upper-triangular factor in the first rows and zero rows below that corner.
The ambient factor is orthogonal. Trefethen--Bau, Theorem 7.1;
Golub--Van Loan, Theorem 5.2.1.
atlas: qr-decomposition (partial) -/
theorem exists_full_qr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hCard : n ≤ m) :
    ∃ W : Matrix (Fin m) (Fin m) ℝ, ∃ R : Matrix (Fin n) (Fin n) ℝ,
      ∃ T : Matrix (Fin m) (Fin n) ℝ,
        HasOrthonormalCols W ∧ R.IsUpperTriangular ∧ (∀ i, 0 ≤ R i i) ∧ W * T = A ∧
          (∀ i j, T (Fin.castLE hCard i) j = R i j) ∧
          (∀ i j, n ≤ i.val → T i j = 0) := by
  let e : Fin n ↪ Fin m := ⟨Fin.castLE hCard, Fin.castLE_injective hCard⟩
  obtain ⟨W, R, T, hW, hUpper, hDiag, hFactor, hCorner, hZero⟩ :=
    exists_full_qr_of_embedding A e
  refine ⟨W, R, T, hW, hUpper, hDiag, hFactor, ?_, ?_⟩
  · intro i j
    exact congrFun (congrFun hCorner i) j
  · intro i j hi
    apply hZero i _ j
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    have hlt := k.isLt
    change k.val = i.val at hv
    omega

end NLAlib
