import NLAlib.ForMathlib.RingTheory.Polynomial.Hermite
import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import NLAlib.Probability.Gaussian.Calculus.PolynomialGrowthIntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.Pi

/-! # Gaussian pairings of Hermite polynomials

Polynomial Gaussian integration by parts proves the exact finite Hermite
pairing. Only polynomial test functions are used, with all integrability
conditions discharged; no bounded-test-function Stein lemma is invoked.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Polynomial
namespace NLAlib

/-- Every real polynomial has an absolutely integrable standard Gaussian
evaluation. -/
theorem integrable_polynomial_eval_gaussianReal (P : ℝ[X]) :
    Integrable (fun x : ℝ => P.eval x) (gaussianReal 0 1) := by
  have he : (fun x : ℝ => P.eval x) =
      fun x => ∑ k ∈ P.support, P.coeff k * x ^ k := by
    funext x
    conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [he]
  exact integrable_finsetSum _ fun k _ => (integrable_pow_gaussianReal k).const_mul _

/-- Standard Gaussian integration by parts holds for every polynomial, whose
value, coordinate product, and derivative are all genuinely integrable. -/
theorem integral_mul_polynomial_eval_gaussianReal (P : ℝ[X]) :
    (∫ x : ℝ, x * P.eval x ∂gaussianReal 0 1) =
      ∫ x : ℝ, P.derivative.eval x ∂gaussianReal 0 1 := by
  have hdiff : Differentiable ℝ (fun x : ℝ => P.eval x) := P.differentiable
  have hderiv : deriv (fun x : ℝ => P.eval x) = fun x => P.derivative.eval x := by
    funext x
    exact P.deriv
  have hx : Integrable (fun x : ℝ => x * P.eval x) (gaussianReal 0 1) := by
    convert integrable_polynomial_eval_gaussianReal (X * P) using 1 <;>
      funext x <;> simp
  have hd : Integrable (deriv (fun x : ℝ => P.eval x)) (gaussianReal 0 1) := by
    rw [hderiv]
    exact integrable_polynomial_eval_gaussianReal P.derivative
  simpa only [hderiv] using
    integral_mul_eq_integral_deriv_gaussianReal_of_integrable
      (fun x : ℝ => P.eval x) hdiff
      (integrable_polynomial_eval_gaussianReal P) hx hd

/-- The real polynomial obtained from Mathlib's integer Hermite polynomial.
This is a coefficient change, without a second Hermite recursion. -/
def realHermite (n : ℕ) : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)

/-- The real Hermite constant is one. -/
@[simp] theorem realHermite_zero : realHermite 0 = 1 := by
  simp [realHermite, Polynomial.hermite_zero]

/-- The real Hermite recursion is multiplication minus differentiation. -/
theorem realHermite_succ (n : ℕ) :
    realHermite (n + 1) = X * realHermite n - (realHermite n).derivative := by
  simp [realHermite, Polynomial.hermite_succ, derivative_map]

/-- Differentiation lowers a real Hermite polynomial with the exact integer
coefficient. -/
theorem derivative_realHermite_succ (n : ℕ) :
    (realHermite (n + 1)).derivative = (n + 1) • realHermite n := by
  change derivative ((hermite (n + 1)).map (Int.castRingHom ℝ)) = _
  rw [derivative_map, Polynomial.derivative_hermite_succ]
  simp [realHermite, nsmul_eq_mul]

/-- Repeated Gaussian polynomial integration by parts transfers the Hermite
factor into the corresponding formal derivative, including degree zero. -/
theorem integral_realHermite_mul_polynomial_eval (n : ℕ) (P : ℝ[X]) :
    (∫ x : ℝ, (realHermite n).eval x * P.eval x ∂gaussianReal 0 1) =
      ∫ x : ℝ, ((Polynomial.derivative^[n]) P).eval x ∂gaussianReal 0 1 := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    have hStein := integral_mul_polynomial_eval_gaussianReal (realHermite n * P)
    have h₁ := integrable_polynomial_eval_gaussianReal ((realHermite n).derivative * P)
    have h₂ := integrable_polynomial_eval_gaussianReal (realHermite n * P.derivative)
    have h₃ := integrable_polynomial_eval_gaussianReal (X * realHermite n * P)
    simp only [derivative_mul, eval_add, eval_mul] at hStein h₁ h₂
    rw [integral_add h₁ h₂] at hStein
    rw [realHermite_succ]
    simp only [eval_sub, eval_mul, eval_X, sub_mul]
    rw [integral_sub (by simpa only [eval_mul, eval_X, mul_assoc] using h₃) h₁]
    rw [Function.iterate_succ_apply, ← ih P.derivative]
    simp only [← mul_assoc] at hStein
    linarith

/-- Changing Hermite coefficients from integers to reals preserves degree. -/
@[simp] theorem natDegree_realHermite (n : ℕ) : (realHermite n).natDegree = n := by
  rw [realHermite, (Polynomial.hermite_monic n).natDegree_map]
  exact Polynomial.natDegree_hermite

/-- The derivative of order equal to the Hermite degree is its factorial. -/
theorem iterate_derivative_realHermite_self (n : ℕ) :
    (Polynomial.derivative^[n]) (realHermite n) = C (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, derivative_realHermite_succ,
      Polynomial.iterate_derivative_smul, ih]
    simp [Nat.factorial_succ, nsmul_eq_mul]

/-- The exact unnormalized scalar Hermite Gram matrix under the standard
Gaussian law. Unequal degrees are orthogonal, and the squared norm is `n!`. -/
theorem integral_realHermite_mul_realHermite (n m : ℕ) :
    (∫ x : ℝ, (realHermite n).eval x * (realHermite m).eval x ∂gaussianReal 0 1) =
      if n = m then (n.factorial : ℝ) else 0 := by
  split_ifs with h
  · subst m
    rw [integral_realHermite_mul_polynomial_eval, iterate_derivative_realHermite_self]
    simp
  · rcases lt_or_gt_of_ne h with hnm | hmn
    · have he : (fun x : ℝ => (realHermite n).eval x * (realHermite m).eval x) =
          fun x => (realHermite m).eval x * (realHermite n).eval x := by
        funext x; exact mul_comm _ _
      rw [he, integral_realHermite_mul_polynomial_eval]
      rw [Polynomial.iterate_derivative_eq_zero (by simpa using hnm)]
      simp
    · rw [integral_realHermite_mul_polynomial_eval]
      rw [Polynomial.iterate_derivative_eq_zero (by simpa using hmn)]
      simp

/-- The normalized probabilists' Hermite function, with respect to the
standard Gaussian probability measure. -/
def hermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  (realHermite n).eval x / Real.sqrt (n.factorial : ℝ)

/-- The normalized constant Hermite function is the constant one. -/
@[simp] theorem hermiteFunction_zero (x : ℝ) : hermiteFunction 0 x = 1 := by
  simp [hermiteFunction]

/-- Hermite functions are continuous polynomial functions. -/
theorem continuous_hermiteFunction (n : ℕ) : Continuous (hermiteFunction n) := by
  unfold hermiteFunction
  exact (realHermite n).continuous.div_const _

/-- Products of scalar Hermite functions are genuinely Gaussian integrable. -/
theorem integrable_hermiteFunction_mul (n m : ℕ) :
    Integrable (fun x => hermiteFunction n x * hermiteFunction m x) (gaussianReal 0 1) := by
  have h := (integrable_polynomial_eval_gaussianReal (realHermite n * realHermite m)).div_const
    (Real.sqrt (n.factorial : ℝ) * Real.sqrt (m.factorial : ℝ))
  convert h using 1 <;> funext x <;> simp [hermiteFunction, div_mul_div_comm]

/-- Scalar normalized Hermite functions form an orthonormal family under the
actual standard Gaussian law. No completeness assertion is needed. -/
theorem integral_hermiteFunction_mul (n m : ℕ) :
    (∫ x, hermiteFunction n x * hermiteFunction m x ∂gaussianReal 0 1) =
      if n = m then 1 else 0 := by
  have he : (fun x => hermiteFunction n x * hermiteFunction m x) =
      fun x => ((realHermite n).eval x * (realHermite m).eval x) /
        (Real.sqrt (n.factorial : ℝ) * Real.sqrt (m.factorial : ℝ)) := by
    funext x
    simp only [hermiteFunction, div_mul_div_comm]
  rw [he, integral_div, integral_realHermite_mul_realHermite]
  split_ifs with h
  · subst m
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _), div_self (by positivity)]
  · exact zero_div _

/-- Independent products of scalar Hermite functions, indexed by their
occupation numbers. -/
def productHermite {ι : Type*} [Fintype ι] (a : ι → ℕ) (x : ι → ℝ) : ℝ :=
  ∏ i, hermiteFunction (a i) (x i)

/-- Tensor Hermite products are continuous. -/
theorem continuous_productHermite {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    Continuous (productHermite a) := by
  unfold productHermite
  exact continuous_finsetProd _ fun i _ =>
    (continuous_hermiteFunction (a i)).comp (continuous_apply i)

/-- Products of tensor Hermite functions are integrable under the finite
standard Gaussian product law. -/
theorem integrable_productHermite_mul {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    Integrable (fun x => productHermite a x * productHermite b x) (gaussianVector ι) := by
  simpa only [productHermite, ← Finset.prod_mul_distrib] using
    Integrable.fintype_prod (fun i => integrable_hermiteFunction_mul (a i) (b i))

/-- Finite product Hermite functions are exactly orthonormal under the
independent standard Gaussian law, including an empty coordinate set. -/
theorem integral_productHermite_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) :
    (∫ x, productHermite a x * productHermite b x ∂gaussianVector ι) =
      if a = b then 1 else 0 := by
  simp only [productHermite, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod
    (fun (i : ι) (t : ℝ) => hermiteFunction (a i) t * hermiteFunction (b i) t)]
  simp_rw [integral_hermiteFunction_mul]
  split_ifs with h
  · subst b
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end NLAlib
