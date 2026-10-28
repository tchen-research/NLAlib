import NLAlib.Polynomial.FunctionApproximation.ChebyshevTensor

/-! # Polynomial form of the normalized Chebyshev basis

The function used in the tensor moment estimates is evaluated from this actual
polynomial, which can also be applied to matrices by polynomial functional calculus.
-/

noncomputable section
open Polynomial
namespace NLAlib

/-- The polynomial underlying the native normalized Chebyshev function. -/
def normalizedChebyshevPolynomial (j : ℕ) : ℝ[X] :=
  C (normalizedChebyshevWeight j) * Chebyshev.T ℝ (j : ℤ)

/-- Evaluation recovers the native normalized Chebyshev function. -/
@[simp] theorem eval_normalizedChebyshevPolynomial (j : ℕ) (x : ℝ) :
    (normalizedChebyshevPolynomial j).eval x = normalizedChebyshev j x := by
  simp [normalizedChebyshevPolynomial, normalizedChebyshev]

/-- Complex evaluation on the real line retains exactly the real normalization. -/
@[simp] theorem eval_map_normalizedChebyshevPolynomial (j : ℕ) (x : ℝ) :
    ((normalizedChebyshevPolynomial j).map Complex.ofRealHom).eval (x : ℂ) =
      (normalizedChebyshev j x : ℂ) := by
  rw [show (x : ℂ) = Complex.ofRealHom x from rfl, eval_map_apply,
    eval_normalizedChebyshevPolynomial]
  rfl

end NLAlib
