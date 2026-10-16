import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Differentiation of polynomial evaluation in a noncommutative algebra

The derivative is the finite sum with every possible insertion position.
No commutativity of the input algebra is assumed. This supports the
matrix divided-difference and rational block calculi.
-/

noncomputable section
open scoped RightActions
namespace Polynomial
variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The derivative of polynomial evaluation in an arbitrary normed algebra,
as a finite sum of continuous linear insertion maps. -/
def frechetDerivative (p : 𝕜[X]) (x : A) : A →L[𝕜] A :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k •
    ∑ j ∈ Finset.range k,
      x ^ (k.pred - j) •> ContinuousLinearMap.id 𝕜 A <• x ^ j

/-- Evaluation of the polynomial derivative is the sum of products with
one occurrence of the direction at every insertion position. -/
theorem frechetDerivative_apply (p : 𝕜[X]) (x h : A) :
    frechetDerivative p x h = ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k • ∑ j ∈ Finset.range k, x ^ (k.pred - j) * h * x ^ j := by
  simp [frechetDerivative, mul_assoc]

/-- Polynomial evaluation has the insertion-sum Fréchet derivative even
when the target algebra is noncommutative. -/
theorem hasFDerivAt_aeval_noncomm (p : 𝕜[X]) (x : A) :
    HasFDerivAt (fun y : A => aeval y p) (frechetDerivative p x) x := by
  have heq : (fun y : A => aeval y p) =
      fun y => ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • y ^ k := by
    funext y
    rw [aeval_eq_sum_range]
  rw [heq]
  exact HasFDerivAt.fun_sum (fun k _ => (hasFDerivAt_pow' k).const_smul (p.coeff k))

/-- Constants have zero polynomial evaluation derivative. -/
@[simp] theorem frechetDerivative_C (c : 𝕜) (x : A) :
    frechetDerivative (C c) x = 0 := by
  apply (hasFDerivAt_aeval_noncomm (C c) x).unique
  convert! (hasFDerivAt_const (𝕜 := 𝕜) (algebraMap 𝕜 A c) x) using 1
  simp only [aeval_C]

/-- The derivative of the variable polynomial is the identity map. -/
@[simp] theorem frechetDerivative_X (x : A) :
    frechetDerivative (X : 𝕜[X]) x = ContinuousLinearMap.id 𝕜 A := by
  apply (hasFDerivAt_aeval_noncomm (X : 𝕜[X]) x).unique
  convert! (hasFDerivAt_id (𝕜 := 𝕜) x) using 1
  funext y
  exact aeval_X y

/-- The insertion derivative is additive in the polynomial. -/
@[simp] theorem frechetDerivative_add (p q : 𝕜[X]) (x : A) :
    frechetDerivative (p + q) x = frechetDerivative p x + frechetDerivative q x := by
  apply (hasFDerivAt_aeval_noncomm (p + q) x).unique
  convert! (hasFDerivAt_aeval_noncomm p x).add (hasFDerivAt_aeval_noncomm q x) using 1
  funext y
  exact map_add (aeval y) p q

/-- The polynomial derivative obeys the noncommutative product rule. -/
theorem frechetDerivative_mul (p q : 𝕜[X]) (x : A) :
    frechetDerivative (p * q) x =
      aeval x p •> frechetDerivative q x + frechetDerivative p x <• aeval x q := by
  apply (hasFDerivAt_aeval_noncomm (p * q) x).unique
  convert! (hasFDerivAt_aeval_noncomm p x).mul' (hasFDerivAt_aeval_noncomm q x) using 1
  funext y
  exact map_mul (aeval y) p q

/-- Algebra homomorphisms transport each insertion in a polynomial
derivative, without requiring continuity of the homomorphism. -/
theorem map_frechetDerivative_apply {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]
    (f : A →ₐ[𝕜] B) (p : 𝕜[X]) (x h : A) :
    f (p.frechetDerivative x h) = p.frechetDerivative (f x) (f h) := by
  simp only [frechetDerivative_apply, map_sum, map_smul, map_mul, map_pow]

end Polynomial
