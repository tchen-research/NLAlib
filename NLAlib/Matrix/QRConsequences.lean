import NLAlib.Matrix.QRExistence
import NLAlib.Matrix.GramSingularValues
import NLAlib.Matrix.ConditionNumber
import NLAlib.Matrix.Gram

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

/-- The Gram matrix of every thin QR factor equals the original Gram matrix,
even at deficient rank. Trefethen--Bau, Theorem 7.1.
atlas: qr-decomposition (partial) -/
theorem transpose_mul_self_eq_of_qr {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) : Rᵀ * R = Aᵀ * A := by
  rw [← hFactor, Matrix.transpose_mul]
  have hGram : Qᵀ * Q = 1 := hQ
  calc
    Rᵀ * R = Rᵀ * (Qᵀ * Q) * R := by rw [hGram, Matrix.mul_one]
    _ = Rᵀ * Qᵀ * (Q * R) := by simp only [Matrix.mul_assoc]

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

/-- Positive-diagonal thin QR pairs of a full-column-rank matrix coincide.
Cholesky uniqueness first identifies the upper factor; invertibility then
identifies the frame. Trefethen--Bau, Theorem 7.2;
Golub--Van Loan, Theorem 5.2.3.
atlas: qr-decomposition (partial) -/
theorem qr_pair_unique {A Q₁ Q₂ : Matrix m n ℝ} {R₁ R₂ : Matrix n n ℝ}
    (hRank : A.rank = Fintype.card n)
    (hQ₁ : HasOrthonormalCols Q₁) (hQ₂ : HasOrthonormalCols Q₂)
    (hUpper₁ : R₁.IsUpperTriangular) (hUpper₂ : R₂.IsUpperTriangular)
    (hDiag₁ : ∀ i, 0 < R₁ i i) (hDiag₂ : ∀ i, 0 < R₂ i i)
    (hFactor₁ : Q₁ * R₁ = A) (hFactor₂ : Q₂ * R₂ = A) : Q₁ = Q₂ ∧ R₁ = R₂ := by
  have hGram := posDef_transpose_mul_self_of_rank_eq_card hRank
  have hFactorT₁ : R₁ᵀ * (R₁ᵀ)ᵀ = Aᵀ * A := by
    simpa only [Matrix.transpose_transpose] using transpose_mul_self_eq_of_qr hQ₁ hFactor₁
  have hFactorT₂ : R₂ᵀ * (R₂ᵀ)ᵀ = Aᵀ * A := by
    simpa only [Matrix.transpose_transpose] using transpose_mul_self_eq_of_qr hQ₂ hFactor₂
  have hRT := cholesky_factor_unique hGram hUpper₁.transpose hUpper₂.transpose
    hDiag₁ hDiag₂ hFactorT₁ hFactorT₂
  have hR : R₁ = R₂ := Matrix.transpose_injective hRT
  refine ⟨?_, hR⟩
  have hUnit := isUnit_of_qr_of_rank_eq_card hQ₁ hFactor₁ hRank
  have hDet := (Matrix.isUnit_iff_isUnit_det R₁).mp hUnit
  calc
    Q₁ = (Q₁ * R₁) * R₁⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hDet, Matrix.mul_one]
    _ = (Q₂ * R₁) * R₁⁻¹ := by rw [hFactor₁, hR, hFactor₂]
    _ = Q₂ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hDet, Matrix.mul_one]

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
  obtain ⟨Q, R, hQ, hUpper, hDiag, hFactor⟩ := exists_qr A hCard
  have hPositive := diag_pos_of_qr_of_rank_eq_card hQ hUpper hDiag hFactor hRank
  refine ⟨(Q, R), ⟨hQ, hUpper, hPositive, hFactor⟩, ?_⟩
  rintro ⟨Q', R'⟩ ⟨hQ', hUpper', hDiag', hFactor'⟩
  obtain ⟨hQEq, hREq⟩ := qr_pair_unique hRank hQ' hQ hUpper' hUpper hDiag' hPositive hFactor' hFactor
  exact Prod.ext hQEq hREq

/-- The native zero-padded singular values of a QR factor are exactly those
of the original matrix at every natural index, with arbitrary finite indices.
Trefethen--Bau, Theorem 7.1; Golub--Van Loan, Theorem 5.2.1.
atlas: qr-decomposition (partial) -/
theorem toEuclideanLin_singularValues_eq_of_qr {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) (k : ℕ) :
    R.toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  apply toEuclideanLin_singularValues_eq_of_gram_eq R A
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    transpose_mul_self_eq_of_qr hQ hFactor

/-- In standard finite coordinates, the library singular-value sequence of
the triangular QR factor equals that of the original matrix at every index.
Trefethen--Bau, Theorem 7.1; Golub--Van Loan, Theorem 5.2.1.
atlas: qr-decomposition (partial) -/
theorem singularValues_eq_of_qr {a b : ℕ} {A Q : Matrix (Fin a) (Fin b) ℝ}
    {R : Matrix (Fin b) (Fin b) ℝ} (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) :
    singularValues R = singularValues A := by
  funext k
  exact toEuclideanLin_singularValues_eq_of_qr hQ hFactor k

/-- QR preserves the total spectral condition number built from the actual
Moore--Penrose inverse, including singular and zero-rank matrices.
Golub--Van Loan, Section 2.6.2; supports `qr-decomposition`.
atlas: qr-decomposition (partial) -/
theorem conditionNumber_eq_of_qr [DecidableEq m] {A Q : Matrix m n ℝ} {R : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (hFactor : Q * R = A) : conditionNumber R = conditionNumber A := by
  rw [← hFactor, conditionNumber_mul_left_of_hasOrthonormalCols Q R hQ]

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
