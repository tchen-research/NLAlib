import NLAlib.Krylov.Quadrature.MomentOrthogonality
import NLAlib.Krylov.Quadrature.JacobiFraction
import NLAlib.Matrix.Structured.JacobiContinuants
import NLAlib.Polynomial.OrthogonalPolynomials.MonicKernelIdentities

/-! # Monic identities of actual signed Lanczos compressions

The actual characteristic polynomials have squared-norm products of the signed
off-diagonals. Their continued-fraction denominator polynomials are the same
characteristic polynomials, independently of basis orientation. The valid index
range distinguishes a stored coupling from the total zero beyond the decomposition.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib.LanczosDecomp

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- The leading actual Lanczos compression has the parent's diagonal and
off-diagonal coefficients on its included indices. -/
theorem T_restrict_eq_jacobiMatrix (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {j : ℕ} (hj : j ≤ q) : (LanczosDecomp.T (D.restrict hj)) = jacobiMatrix D.alpha D.beta j := by
  change ArnoldiDecomp.H (D.restrict hj) = _
  rw [ArnoldiDecomp.H_restrict, show ArnoldiDecomp.H D = D.T from rfl, D.T_eq_jacobiMatrix hA]
  ext i k
  simp only [jacobiMatrix, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_castLE]

/-- The actual finite Jacobi denominator polynomial equals the monic characteristic
polynomial of every leading signed Lanczos compression, including order zero and
the displayed terminal order. Source: Gautschi (2004), Theorem 1.34; (OF8), (OF26).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem jacobiContinuant_eq_charpoly_restrict_T (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {j : ℕ} (hj : j ≤ q) :
    jacobiContinuant D.alpha D.beta j = (LanczosDecomp.T (D.restrict hj)).charpoly := by
  rw [D.T_restrict_eq_jacobiMatrix hA hj, charpoly_jacobiMatrix_eq_jacobiContinuant]

/-- The squared norm of an actual monic leading characteristic polynomial is the
starting-vector mass times the product of squared stored off-diagonals. Arbitrary
Lanczos basis signs are allowed; the order is below the displayed decomposition
size so every required coupling is stored. Source: Gautschi (2004), Theorem 1.27; (OF8).
atlas: monic-orthogonal-recurrence (partial) -/
theorem integral_sq_charpoly_restrict_T_eq_norm_sq_mul_prod_beta_sq
    (D : LanczosDecomp A b q) (hA : A.IsHermitian) {j : ℕ} (hj : j < q) :
    (∫ x, ((LanczosDecomp.T (D.restrict hj.le)).charpoly.eval x) ^ 2 ∂spectralMeasure hA b) =
      ‖WithLp.toLp 2 b‖ ^ 2 * ∏ k ∈ Icc 1 j, D.beta k ^ 2 := by
  let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
  let χ := (LanczosDecomp.T (D.restrict hj.le)).charpoly
  let c := (D.poly 0).leadingCoeff
  let t := ∏ k ∈ Icc 1 j, D.beta k
  have hLC (r : ℝ) (p : ℝ[X]) : L (C r * p) = r * L p := by
    rw [C_mul', map_smul]
    rfl
  have hC (r : ℝ) : L (C r) = r * L 1 := by simpa only [mul_one] using hLC r 1
  have hmass : L 1 = ‖WithLp.toLp 2 b‖ ^ 2 := by
    rw [polynomialIntegral_apply, integral_eval_spectralMeasure, norm_toLp_sq_eq_dotProduct_self]
    simp
  have hpoly (k : ℕ) (hk : k < q) : L (D.poly k ^ 2) = 1 := by
    simpa only [L, polynomialIntegral_apply, eval_pow, pow_two, eval_mul, if_true] using
      (D.integral_poly_mul_poly hA (i := k) (j := k) hk)
  have hpn : (D.poly 0).natDegree = 0 :=
    natDegree_eq_of_degree_eq_some (D.degree_poly (by omega))
  have hp0 : D.poly 0 = C c := by
    simpa only [c, leadingCoeff, hpn] using eq_C_of_natDegree_eq_zero hpn
  have hc0 := hpoly 0 (by omega)
  rw [hp0, ← map_pow C c, hC, hmass] at hc0
  have hc : c ≠ 0 := by intro h; simp [h] at hc0
  have he := congrArg (fun p : ℝ[X] => L (p ^ 2)) (D.charpoly_restrict_T_mul_poly_zero hA hj)
  rw [hp0] at he
  change L ((χ * C c) ^ 2) = L ((C t * D.poly j) ^ 2) at he
  rw [show (χ * C c) ^ 2 = C (c ^ 2) * χ ^ 2 by rw [map_pow]; ring,
    show (C t * D.poly j) ^ 2 = C (t ^ 2) * D.poly j ^ 2 by rw [map_pow]; ring,
    hLC, hLC, hpoly j hj, mul_one] at he
  have hm : L (χ ^ 2) = ‖WithLp.toLp 2 b‖ ^ 2 * t ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc)
    rw [he, ← mul_assoc, hc0, one_mul]
  simpa only [L, χ, polynomialIntegral_apply, eval_pow, t, prod_pow] using hm

end NLAlib.LanczosDecomp
