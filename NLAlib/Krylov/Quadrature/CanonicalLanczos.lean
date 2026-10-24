import NLAlib.Krylov.Quadrature.MonicLanczosCoefficients
import NLAlib.Krylov.Processes.LanczosRecurrence
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiCoefficients

/-! # Positive Lanczos compressions are the canonical moment Jacobi matrices

Monic recurrence coefficients already identify the diagonals and squared signed
off-diagonals. Nonnegative Lanczos off-diagonals select the canonical square roots,
giving equality of the actual matrices, not only their spectra. The actual three-term
Lanczos process has this sign convention, including empty order.

Source: Gautschi (2004), §§1.3 and 2.2.3.
Atlas: `discrete-measure-jacobi-matrix`.
-/

noncomputable section
open Matrix Polynomial MeasureTheory
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Nonnegative Lanczos couplings identify the actual compression with the canonical
moment Jacobi matrix of its spectral measure. Empty order is included.
Source: Gautschi (2004), Theorem 1.27 and §2.2.3.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem LanczosDecomp.T_eq_orthogonalPolynomialJacobiMatrix_of_beta_nonneg
    {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ} (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hbeta : ∀ j < q, 0 ≤ D.beta j) :
    D.T = orthogonalPolynomialJacobiMatrix
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) q := by
  let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
  have hL (k : ℕ) (hk : k ≤ q) : hankelMomentDet L k ≠ 0 := by
    apply hankelMomentDet_ne_zero_of_le_support_encard
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hk.trans D.le_krylovGrade
  have hH (k : ℕ) (hk : k < q) : 0 < orthogonalPolynomialNorm L k := by
    apply orthogonalPolynomialNorm_pos_of_lt_support_encard
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast (Nat.succ_le_of_lt hk).trans D.le_krylovGrade
  rw [D.T_eq_jacobiMatrix hA, orthogonalPolynomialJacobiMatrix_eq_jacobiMatrix L q hL hH]
  ext i j
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with hij hupper hlower
  · exact (D.orthogonalRecurrenceAlpha_spectralMeasure_eq_alpha hA i.isLt).symm
  · rw [D.orthogonalRecurrenceBeta_spectralMeasure_eq_beta_sq hA j.isLt,
      Real.sqrt_sq (hbeta j.val j.isLt)]
  · rw [D.orthogonalRecurrenceBeta_spectralMeasure_eq_beta_sq hA i.isLt,
      Real.sqrt_sq (hbeta i.val i.isLt)]
  · rfl

/-- The actual positively normalized Lanczos algorithm yields the canonical moment Jacobi
matrix of its spectral measure, at every order up to grade.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem T_arnoldiDecomp_eq_orthogonalPolynomialJacobiMatrix
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) {q : ℕ}
    (hq : q ≤ krylovGrade A b) :
    LanczosDecomp.T (arnoldiDecomp A b q hq) = orthogonalPolynomialJacobiMatrix
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) q := by
  apply LanczosDecomp.T_eq_orthogonalPolynomialJacobiMatrix_of_beta_nonneg _ hA
  intro j hj
  rw [← lanczosBeta_eq_beta hA b hq hj]
  exact lanczosBeta_nonneg A b j

/-- The Jacobi matrix assembled from the actual Lanczos recursion's coefficients is the
actual compression at every valid order. Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem jacobiMatrix_lanczosAlpha_lanczosBeta_eq_T
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) {q : ℕ}
    (hq : q ≤ krylovGrade A b) :
    jacobiMatrix (lanczosAlpha A b) (lanczosBeta A b) q =
      LanczosDecomp.T (arnoldiDecomp A b q hq) := by
  rw [LanczosDecomp.T_eq_jacobiMatrix _ hA]
  ext i j
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with hij hupper hlower
  · exact lanczosAlpha_eq_alpha hA b hq i.isLt
  · exact lanczosBeta_eq_beta hA b hq j.isLt
  · exact lanczosBeta_eq_beta hA b hq i.isLt
  · rfl

end NLAlib
