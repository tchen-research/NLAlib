import NLAlib.ForMathlib.Analysis.PolynomialDifferential
import NLAlib.Matrix.Functions.DividedDifferences
import NLAlib.Matrix.Functions.DiagonalFilter
import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# Polynomial matrix derivatives in diagonal coordinates

The noncommutative product rule gives the divided-difference Hadamard
formula by polynomial induction. Repeated nodes require no separate
limiting argument. Tropp (2022), Theorem 14.13.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator RightActions
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In diagonal coordinates the polynomial derivative is multiplication
entry by entry by its confluent divided-difference matrix. -/
theorem frechetDerivative_diagonal_apply (p : ℝ[X]) (ev : n → ℝ) (H : Matrix n n ℂ) :
    p.frechetDerivative (diagonal (fun i => (ev i : ℂ))) H =
      Matrix.of (fun i j => (((p.dividedDifference (ev i)).eval (ev j) : ℝ) : ℂ) * H i j) := by
  induction p using Polynomial.induction_on with
  | C a => ext i j; simp
  | add p q hp hq =>
    rw [Polynomial.frechetDerivative_add, _root_.add_apply, hp, hq]
    ext i j
    simp only [Matrix.add_apply, Matrix.of_apply, Polynomial.dividedDifference_add,
      Polynomial.eval_add, Complex.ofReal_add, add_mul]
  | monomial k a ih =>
    let p : ℝ[X] := C a * X ^ k
    have hpoly : C a * X ^ (k + 1) = p * X := by dsimp [p]; rw [pow_succ]; ring
    rw [hpoly, Polynomial.frechetDerivative_mul, Polynomial.frechetDerivative_X,
      Polynomial.aeval_X]
    change aeval (diagonal (fun i => (ev i : ℂ))) p * H +
      (p.frechetDerivative (diagonal (fun i => (ev i : ℂ))) H) *
        diagonal (fun i => (ev i : ℂ)) = _
    have hdiag : aeval (diagonal (fun i => (ev i : ℂ))) p =
        diagonal (fun i => ((p.eval (ev i) : ℝ) : ℂ)) :=
      aeval_diagonal_ofReal (𝕜 := ℂ) ev p
    rw [ih, hdiag]
    ext i j
    rw [show p * X = X * p from mul_comm _ _]
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply,
      Polynomial.dividedDifference_X_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, Complex.ofReal_add, Complex.ofReal_mul]
    ring

end NLAlib
