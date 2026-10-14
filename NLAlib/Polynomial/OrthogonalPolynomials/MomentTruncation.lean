import NLAlib.Polynomial.OrthogonalPolynomials.MomentCoordinates
import NLAlib.Polynomial.Quadrature.MomentGauss
import NLAlib.ForMathlib.Analysis.Calculus.LagrangeContinuity

/-!
# Moment truncation preserves finite Gauss data

The first `2n` moments determine every order at most `n`, every included
recurrence coefficient, the Jacobi matrix, and its canonical Gauss nodes and
weights. The equalities hold even at early singular systems because the
definitions are total. Source: AQ22–AQ23 in the operator re-derivations.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib

/-- The first `2n` monomial moments of a polynomial functional. -/
def finiteMomentVector (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : Fin (2 * n) → ℝ :=
  fun i => L (X ^ i.val)

/-- Truncating above degree `2n-1` preserves each lower-order Hankel matrix. -/
theorem hankelMomentMatrix_finiteMomentVector_eq (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k ≤ n) :
    hankelMomentMatrix (finiteMomentFunctional (finiteMomentVector L n)) k = hankelMomentMatrix L k := by
  ext i j
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  rw [degree_X_pow]
  exact_mod_cast (show i.val + j.val < 2 * n by have := i.isLt; have := j.isLt; omega)

/-- Every canonical polynomial through order `n` depends only on `2n` moments. -/
theorem monicOrthogonalPolynomial_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k ≤ n) :
    monicOrthogonalPolynomial (finiteMomentFunctional (finiteMomentVector L n)) k =
      monicOrthogonalPolynomial L k := by
  apply monicOrthogonalPolynomial_eq_of_moments_eq
  intro j hj
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  rw [degree_X_pow]
  exact_mod_cast (show j < 2 * n by omega)

/-- Included squared monic norms depend only on the same finite moments. -/
theorem orthogonalPolynomialNorm_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k < n) :
    orthogonalPolynomialNorm (finiteMomentFunctional (finiteMomentVector L n)) k =
      orthogonalPolynomialNorm L k := by
  unfold orthogonalPolynomialNorm
  rw [monicOrthogonalPolynomial_finiteMomentVector_eq L hk.le]
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  rw [degree_pow, degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
    natDegree_monicOrthogonalPolynomial, nsmul_eq_mul]
  exact_mod_cast (show 2 * k < 2 * n by omega)

/-- Included diagonal coefficients are exactly those of the finite moment vector. -/
theorem orthogonalRecurrenceAlpha_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k < n) :
    orthogonalRecurrenceAlpha (finiteMomentFunctional (finiteMomentVector L n)) k =
      orthogonalRecurrenceAlpha L k := by
  unfold orthogonalRecurrenceAlpha
  rw [orthogonalPolynomialNorm_finiteMomentVector_eq L hk,
    monicOrthogonalPolynomial_finiteMomentVector_eq L hk.le]
  congr 1
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  rw [degree_mul, degree_X, degree_pow,
    degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
    natDegree_monicOrthogonalPolynomial, nsmul_eq_mul]
  exact_mod_cast (show 1 + 2 * k < 2 * n by omega)

/-- Included subdiagonal coefficients, including the zero-order boundary,
are exactly those determined by the finite moment vector. -/
theorem orthogonalRecurrenceBeta_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k < n) :
    orthogonalRecurrenceBeta (finiteMomentFunctional (finiteMomentVector L n)) k =
      orthogonalRecurrenceBeta L k := by
  unfold orthogonalRecurrenceBeta
  split_ifs
  · rfl
  · rw [orthogonalPolynomialNorm_finiteMomentVector_eq L hk,
      orthogonalPolynomialNorm_finiteMomentVector_eq L (by omega : k - 1 < n)]

/-- Included normalized polynomials are preserved, even when their norms vanish. -/
theorem orthonormalMomentPolynomial_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k < n) :
    orthonormalMomentPolynomial (finiteMomentFunctional (finiteMomentVector L n)) k =
      orthonormalMomentPolynomial L k := by
  simp only [orthonormalMomentPolynomial, orthogonalPolynomialNorm_finiteMomentVector_eq L hk,
    monicOrthogonalPolynomial_finiteMomentVector_eq L hk.le]

private theorem degree_orthonormalMomentPolynomial_le (L : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) :
    (orthonormalMomentPolynomial L k).degree ≤ k := by
  rw [orthonormalMomentPolynomial, C_mul']
  apply (degree_smul_le _ _).trans_eq
  rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
    natDegree_monicOrthogonalPolynomial]

/-- The actual normalized multiplication matrix is determined by `2n` moments. -/
theorem orthogonalPolynomialJacobiMatrix_finiteMomentVector_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    orthogonalPolynomialJacobiMatrix (finiteMomentFunctional (finiteMomentVector L n)) n =
      orthogonalPolynomialJacobiMatrix L n := by
  ext i j
  simp only [orthogonalPolynomialJacobiMatrix,
    orthonormalMomentPolynomial_finiteMomentVector_eq L i.isLt,
    orthonormalMomentPolynomial_finiteMomentVector_eq L j.isLt]
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  apply (degree_mul_le _ _).trans_lt
  apply (add_le_add ((degree_mul_le _ _).trans
    (add_le_add (by rw [degree_X]) (degree_orthonormalMomentPolynomial_le L j.val)))
    (degree_orthonormalMomentPolynomial_le L i.val)).trans_lt
  exact_mod_cast (show 1 + j.val + i.val < 2 * n by have := i.isLt; have := j.isLt; omega)

/-- The canonical nodes are determined by `2n` moments, with their fixed indexing. -/
theorem momentGaussNodes_finiteMomentVector_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    momentGaussNodes (finiteMomentFunctional (finiteMomentVector L n)) n = momentGaussNodes L n := by
  funext i
  exact Matrix.IsHermitian.eigenvalues₀_congr
    (isHermitian_orthogonalPolynomialJacobiMatrix (finiteMomentFunctional (finiteMomentVector L n)) n)
    (isHermitian_orthogonalPolynomialJacobiMatrix L n)
    (orthogonalPolynomialJacobiMatrix_finiteMomentVector_eq L n)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

/-- The canonical integrated-cardinal weights are determined by `2n` moments. -/
theorem momentGaussWeights_finiteMomentVector_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    momentGaussWeights (finiteMomentFunctional (finiteMomentVector L n)) n = momentGaussWeights L n := by
  funext i
  unfold momentGaussWeights
  rw [momentGaussNodes_finiteMomentVector_eq]
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  apply (Lagrange.degree_basis_le_of_mem _ (mem_univ i)).trans_lt
  simp only [card_univ, Fintype.card_fin]
  exact_mod_cast (show n - 1 < 2 * n by have := i.isLt; omega)

end NLAlib
