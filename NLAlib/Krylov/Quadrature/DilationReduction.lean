import NLAlib.Krylov.Quadrature.DilationWeightedMoments
import NLAlib.Polynomial.OrthogonalPolynomials.SquareReduction

/-! # Actual Lanczos polynomials of the symmetric dilation

The native spectral-measure identities reduce even and odd monic Lanczos characteristic
polynomials to the left and right normal matrices. The support threshold comes from
each valid decomposition, so finite Krylov termination is included.
-/

noncomputable section
open Matrix Polynomial MeasureTheory
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Every defined monic recurrence diagonal of the actual upper-seed dilation measure
vanishes, including its support-termination order. Source: Gautschi (2004), Theorem 1.17.
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem orthogonalRecurrenceAlpha_spectralMeasure_dilation_eq_zero
    (B : Matrix m n ℝ) (u : m → ℝ) (k : ℕ)
    (hk : k ≤ krylovGrade (dilation B) (Sum.elim u 0)) :
    orthogonalRecurrenceAlpha
      (polynomialIntegral (spectralMeasure (isHermitian_dilation B) (Sum.elim u 0))
        (hasPolynomialMoments_spectralMeasure _ _)) k = 0 := by
  apply orthogonalRecurrenceAlpha_polynomialIntegral_eq_zero
    (hasPolynomialMoments_spectralMeasure _ _) (map_neg_spectralMeasure_dilation B u)
  rw [support_encard_spectralMeasure_eq_krylovGrade]
  exact_mod_cast hk

namespace LanczosDecomp

/-- At every valid even order, the actual augmented Lanczos monic polynomial is the
left-normal spectral measure's canonical monic polynomial composed with `X²`.
Source: Gautschi (2004), Theorem 1.18 and Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem charpoly_T_dilation_two_mul_eq_comp_X_sq
    {B : Matrix m n ℝ} {u : m → ℝ} {k : ℕ}
    (D : NLAlib.LanczosDecomp (dilation B) (Sum.elim u 0) (2 * k)) :
    D.T.charpoly =
      (monicOrthogonalPolynomial
        (polynomialIntegral (spectralMeasure (isHermitian_mul_conjTranspose_self B) u)
          (hasPolynomialMoments_spectralMeasure _ _)) k).comp (X ^ 2) := by
  let μ := spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)
  let hμ := hasPolynomialMoments_spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)
  have hk : (2 * k : ℕ∞) ≤ μ.support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast D.le_krylovGrade
  have h := monicOrthogonalPolynomial_two_mul_eq_comp_X_sq hμ
    (map_neg_spectralMeasure_dilation B u) k hk
  simp only [map_sq_spectralMeasure_dilation] at h
  rw [← D.monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T (isHermitian_dilation B)]
  exact h

/-- At every valid odd order, the actual augmented Lanczos monic polynomial is `X`
times the right-normal spectral measure's canonical monic polynomial at `Bᵀu`,
composed with `X²`. Source: Gautschi (2004), Theorem 1.18 and Section 2.2; (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem charpoly_T_dilation_two_mul_add_one_eq_X_mul_comp_X_sq
    {B : Matrix m n ℝ} {u : m → ℝ} {k : ℕ}
    (D : NLAlib.LanczosDecomp (dilation B) (Sum.elim u 0) (2 * k + 1)) :
    D.T.charpoly = X *
      (monicOrthogonalPolynomial
        (polynomialIntegral
          (spectralMeasure (isHermitian_conjTranspose_mul_self B) (Bᵀ *ᵥ u))
          (hasPolynomialMoments_spectralMeasure _ _)) k).comp (X ^ 2) := by
  let μ := spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)
  let hμ := hasPolynomialMoments_spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)
  have hk : (2 * k + 1 : ℕ∞) ≤ μ.support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast D.le_krylovGrade
  have h := monicOrthogonalPolynomial_two_mul_add_one_eq_X_mul_comp_X_sq hμ
    (map_neg_spectralMeasure_dilation B u) k hk
  simp only [map_sq_withDensity_sq_spectralMeasure_dilation] at h
  rw [← D.monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T (isHermitian_dilation B)]
  exact h

end LanczosDecomp
end NLAlib
