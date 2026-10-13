import NLAlib.Matrix.Factorizations.QRExistence
import NLAlib.Matrix.Spectral.GramSingularValues
import NLAlib.Matrix.Perturbation.ConditionNumber
import NLAlib.Matrix.Basic.Gram
/-!
# QR uniqueness and spectral identities

QR preserves the actual Gram matrix, native singular-value sequence and
Moore--Penrose condition number. Full column rank gives a positive diagonal,
a unique pair and the actual orthogonal range projector. Source:
Trefethen--Bau, Theorems 7.1--7.2; Golub--Van Loan, Theorems 5.2.1 and 5.2.3.
Atlas: `qr-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [LinearOrder n]

/-- Full column rank makes the actual Gram matrix positive definite,
including empty column spaces. Rank identity and the PSD invertibility
criterion; supports `qr-decomposition`. -/
theorem posDef_transpose_mul_self_of_rank_eq_card {A : Matrix m n ℝ}
    (hRank : A.rank = Fintype.card n) : (Aᵀ * A).PosDef := by
  have hPSD : (Aᵀ * A).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  apply hPSD.posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  apply det_ne_zero_of_rank_eq
  rwa [Matrix.rank_transpose_mul_self]

/-- Full column rank makes every square thin QR factor invertible.
Trefethen--Bau, Theorem 7.2; supports `qr-decomposition`. -/
theorem isUnit_of_qr_of_rank_eq_card {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A)
    (hRank : A.rank = Fintype.card n) : IsUnit R := by
  apply (Matrix.isUnit_iff_isUnit_det R).mpr
  apply isUnit_iff_ne_zero.mpr
  apply det_ne_zero_of_rank_eq
  rw [← Matrix.rank_transpose_mul_self R, transpose_mul_self_eq_of_qr hQ hFactor,
    Matrix.rank_transpose_mul_self A, hRank]

/-- A nonnegative upper-triangular QR diagonal is strictly positive under
full column rank, also in empty dimension. Trefethen--Bau, Theorem 7.2.
atlas: qr-decomposition (partial) -/
theorem diag_pos_of_qr_of_rank_eq_card {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hUpper : R.IsUpperTriangular)
    (hDiag : ∀ i, 0 ≤ R i i) (hFactor : Q * R = A)
    (hRank : A.rank = Fintype.card n) : ∀ i, 0 < R i i := by
  have hGram := posDef_transpose_mul_self_of_rank_eq_card hRank
  have hFactorT : Rᵀ * (Rᵀ)ᵀ = Aᵀ * A := by
    simpa only [Matrix.transpose_transpose] using transpose_mul_self_eq_of_qr hQ hFactor
  exact diag_pos_of_isLowerTriangular_of_isUnit (L := Rᵀ) hUpper.transpose
    (isUnit_of_mul_transpose_eq_posDef hGram hFactorT) hDiag

/-- Full column rank gives a unique thin QR pair with positive upper diagonal.
This is uniqueness of both actual matrices, not only of their Grams.
Trefethen--Bau, Theorem 7.2; Golub--Van Loan, Theorem 5.2.3.
atlas: qr-decomposition (partial) -/
theorem existsUnique_qr_of_rank_eq_card (A : Matrix m n ℝ)
    (hRank : A.rank = Fintype.card n) :
    ∃! qr : Matrix m n ℝ × Matrix n n ℝ,
      HasOrthonormalCols qr.1 ∧ qr.2.IsUpperTriangular ∧
        (∀ i, 0 < qr.2 i i) ∧ qr.1 * qr.2 = A := by
  have hCard : Fintype.card n ≤ Fintype.card m := by
    rw [← hRank]
    exact Matrix.rank_le_card_height A
  obtain ⟨Q, R, ⟨hFactor, hQ, hUpper⟩, hDiag⟩ := exists_isQR A hCard
  replace hFactor := hFactor.symm
  have hPositive := diag_pos_of_qr_of_rank_eq_card hQ hUpper hDiag hFactor hRank
  refine ⟨(Q, R), ⟨hQ, hUpper, hPositive, hFactor⟩, ?_⟩
  rintro ⟨Q', R'⟩ ⟨hQ', hUpper', hDiag', hFactor'⟩
  obtain ⟨hQEq, hREq⟩ :=
    IsQR.eq_of_diag_pos ⟨hFactor'.symm, hQ', hUpper'⟩ ⟨hFactor.symm, hQ, hUpper⟩ hDiag' hPositive
  exact Prod.ext hQEq hREq

/-- The zero-padded singular values of the triangular QR factor are exactly those of the
original matrix at every index, on arbitrary finite indices.
Trefethen--Bau, Theorem 7.1; Golub--Van Loan, Theorem 5.2.1.
atlas: qr-decomposition (partial) -/
theorem singularValues_eq_of_qr {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) :
    singularValues R = singularValues A := by
  funext k
  apply singularValues_eq_of_gram_eq R A
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    transpose_mul_self_eq_of_qr hQ hFactor

/-- QR preserves the total spectral condition number built from the actual
Moore--Penrose inverse, including singular and zero-rank matrices.
Golub--Van Loan, Section 2.6.2; supports `qr-decomposition`.
atlas: qr-decomposition (partial) -/
theorem moorePenroseConditionNumber_eq_of_qr [DecidableEq m] {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) : moorePenroseConditionNumber R = moorePenroseConditionNumber A := by
  rw [← hFactor, moorePenroseConditionNumber_mul_left_of_hasOrthonormalCols Q R hQ]

/-- Under full column rank, the QR frame projector is the actual
Moore--Penrose orthogonal range projector. Trefethen--Bau, Theorem 7.2;
Golub--Van Loan, Theorem 5.2.3.
atlas: qr-decomposition (partial) -/
theorem mul_transpose_eq_mul_moorePenroseInverse_of_qr_of_rank_eq_card
    {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A)
    (hRank : A.rank = Fintype.card n) : Q * Qᵀ = A * moorePenroseInverse A := by
  classical
  have hUnit := isUnit_of_qr_of_rank_eq_card hQ hFactor hRank
  have hDet := (Matrix.isUnit_iff_isUnit_det R).mp hUnit
  rw [← hFactor, moorePenroseInverse_mul_left_of_hasOrthonormalCols Q R hQ,
    moorePenroseInverse_eq_inv_of_isUnit R hUnit]
  calc
    Q * Qᵀ = Q * (R * R⁻¹) * Qᵀ := by rw [Matrix.mul_nonsing_inv _ hDet, Matrix.mul_one]
    _ = Q * R * (R⁻¹ * Qᵀ) := by simp only [Matrix.mul_assoc]

end NLAlib
