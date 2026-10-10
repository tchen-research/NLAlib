import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Differentiation of matrix inverses and inverse trace powers

Finite matrix calculus for the operator proof of the smallest Wishart eigenvalue
bound (atlas wishart-lambda-min-tail). Matrix inversion is differentiated on
the open set of invertible matrices; no eigenvalue density is involved.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative of an invertible matrix curve is obtained by multiplication
on both sides by its inverse. Source: the Banach algebra inverse derivative;
atlas wishart-lambda-min-tail (operator calculus helper). -/
theorem hasDerivAt_matrix_inv {A : ℝ → Matrix ι ι ℝ}
    {A' : Matrix ι ι ℝ} {t : ℝ} (hA : HasDerivAt A A' t)
    (hunit : IsUnit (A t)) :
    HasDerivAt (fun x => (A x)⁻¹) (-(A t)⁻¹ * A' * (A t)⁻¹) t := by
  rcases hunit with ⟨u, hu⟩
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hi
  have hi' := hi.comp_hasDerivAt t hA
  convert! hi' using 1
  · funext x
    exact Matrix.nonsing_inv_eq_ringInverse (A x)
  · rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
    change -(↑(u⁻¹) : Matrix ι ι ℝ) * A' * (↑(u⁻¹) : Matrix ι ι ℝ) =
      -((↑(u⁻¹) : Matrix ι ι ℝ) * A' * (↑(u⁻¹) : Matrix ι ι ℝ))
    simp only [neg_mul]

/-- Cyclicity of trace collapses the derivative of a noncommutative matrix
power to one trace term. Source: ported from SparseFockFormal,
`TracePowerConvexity.trace_power_derivative_sum`; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem trace_power_derivative_sum (C B : Matrix ι ι ℝ) (n : ℕ) :
    Matrix.trace (∑ i ∈ Finset.range n, C ^ (n.pred - i) * B * C ^ i) =
      (n : ℝ) * Matrix.trace (B * C ^ (n - 1)) := by
  by_cases hn : n = 0
  · subst n; simp
  · rw [Matrix.trace_sum]
    have hterm (i : ℕ) (hi : i ∈ Finset.range n) :
        Matrix.trace (C ^ (n.pred - i) * B * C ^ i) =
          Matrix.trace (B * C ^ (n - 1)) := by
      rw [Matrix.trace_mul_comm (C ^ (n.pred - i) * B) (C ^ i),
        ← Matrix.mul_assoc, Matrix.trace_mul_comm (C ^ i * C ^ (n.pred - i)) B,
        ← pow_add]
      rw [Finset.mem_range] at hi
      simp only [Nat.pred_eq_sub_one]
      rw [show i + (n - 1 - i) = n - 1 by omega]
    calc _ = ∑ _i ∈ Finset.range n, Matrix.trace (B * C ^ (n - 1)) := by
          apply Finset.sum_congr rfl
          intro i hi; exact hterm i hi
      _ = _ := by simp

/-- Trace of a differentiable matrix power has the usual scalar-looking
derivative after cyclicity is used. Source: ported from SparseFockFormal,
`TracePowerConvexity.hasDerivAt_tracePowerAlong`, generalized to matrix curves;
atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem hasDerivAt_matrix_trace_pow {A : ℝ → Matrix ι ι ℝ}
    {A' : Matrix ι ι ℝ} {t : ℝ} (hA : HasDerivAt A A' t) (n : ℕ) :
    HasDerivAt (fun x => Matrix.trace (A x ^ n))
      ((n : ℝ) * Matrix.trace (A' * A t ^ (n - 1))) t := by
  let tr : Matrix ι ι ℝ →L[ℝ] ℝ := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have htrace := (hasDerivAt_const t tr).clm_apply (hA.fun_pow' n)
  simp only [_root_.zero_apply, zero_add] at htrace
  convert! htrace using 1
  · exact (trace_power_derivative_sum (A t) A' n).symm

/-- Along an invertible matrix curve, the derivative of `tr(A⁻ⁿ)` is
`-n tr(A⁻⁽ⁿ⁺¹⁾ A')`. Source: inverse derivative and trace cyclicity;
atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem hasDerivAt_matrix_trace_inv_pow {A : ℝ → Matrix ι ι ℝ}
    {A' : Matrix ι ι ℝ} {t : ℝ} (hA : HasDerivAt A A' t)
    (hunit : IsUnit (A t)) (n : ℕ) :
    HasDerivAt (fun x => Matrix.trace ((A x)⁻¹ ^ n))
      (-(n : ℝ) * Matrix.trace ((A t)⁻¹ ^ (n + 1) * A')) t := by
  have h := hasDerivAt_matrix_trace_pow (hasDerivAt_matrix_inv hA hunit) n
  by_cases hn : n = 0
  · simpa [hn] using h
  · have htrace : Matrix.trace ((-(A t)⁻¹ * A' * (A t)⁻¹) * (A t)⁻¹ ^ (n - 1)) =
        -Matrix.trace ((A t)⁻¹ ^ (n + 1) * A') := by
      simp only [neg_mul, Matrix.trace_neg]
      rw [Matrix.trace_mul_cycle ((A t)⁻¹ * A') (A t)⁻¹ ((A t)⁻¹ ^ (n - 1)),
        ← Matrix.mul_assoc]
      rw [Matrix.trace_mul_cycle ((A t)⁻¹ ^ (n - 1) * (A t)⁻¹) A' (A t)⁻¹,
        ← Matrix.mul_assoc, ← pow_succ', ← pow_succ]
      rw [show n - 1 + 1 = n by omega]
    rw [htrace] at h
    simpa only [mul_neg, neg_mul] using h

set_option maxHeartbeats 800000 in
/-- Cyclic matrix inverse powers give an explicit quadratic trace kernel
after differentiating. Source: inverse derivative and finite power rule;
atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem trace_inv_power_derivative_sum (R B : Matrix ι ι ℝ) (n : ℕ) :
    Matrix.trace ((∑ i ∈ Finset.range (n + 1),
      R ^ ((n + 1).pred - i) * (-R * B * R) * R ^ i) * B) =
      -∑ i ∈ Finset.range (n + 1),
        Matrix.trace (R ^ (n - i + 1) * B * R ^ (i + 1) * B) := by
  simp only [Finset.sum_mul, Matrix.trace_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.pred_succ, neg_mul, mul_neg, Matrix.trace_neg]
  apply congrArg (fun M : Matrix ι ι ℝ => -Matrix.trace M)
  calc R ^ (n - i) * (R * B * R) * R ^ i * B
      = (R ^ (n - i) * R) * B * (R * R ^ i) * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← pow_succ, ← pow_succ']

/-- The directional trace term in an inverse-power derivative has the
negative Hessian kernel as derivative. Source: inverse derivative and
noncommutative power rule; atlas `wishart-lambda-min-tail` (operator calculus
helper), generalized to non-affine curves. -/
theorem hasDerivAt_matrix_trace_inv_pow_mul {A D : ℝ → Matrix ι ι ℝ}
    {D' : Matrix ι ι ℝ} {t : ℝ} (hA : HasDerivAt A (D t) t)
    (hD : HasDerivAt D D' t) (hunit : IsUnit (A t)) (n : ℕ) :
    HasDerivAt (fun x => Matrix.trace ((A x)⁻¹ ^ (n + 1) * D x))
      ((-∑ i ∈ Finset.range (n + 1), Matrix.trace ((A t)⁻¹ ^ (n - i + 1) *
        D t * (A t)⁻¹ ^ (i + 1) * D t)) + Matrix.trace ((A t)⁻¹ ^ (n + 1) * D')) t := by
  have hpow := (hasDerivAt_matrix_inv hA hunit).fun_pow' (n + 1)
  let tr : Matrix ι ι ℝ →L[ℝ] ℝ := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have htrace := (hasDerivAt_const t tr).clm_apply (hpow.mul hD)
  simp only [_root_.zero_apply, zero_add] at htrace
  convert! htrace using 1
  · simp only [tr, LinearMap.coe_toContinuousLinearMap']
    change _ = Matrix.trace (_ + _)
    rw [Matrix.trace_add, trace_inv_power_derivative_sum]

/-- Along an affine matrix line, the directional inverse-power trace has
the negative Hessian kernel as derivative. Source: operator tail proof;
atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem hasDerivAt_matrix_trace_inv_pow_mul_const (A B : Matrix ι ι ℝ)
    (n : ℕ) (t : ℝ) (hunit : IsUnit (A + t • B)) :
    HasDerivAt (fun x => Matrix.trace ((A + x • B)⁻¹ ^ (n + 1) * B))
      (-∑ i ∈ Finset.range (n + 1),
        Matrix.trace ((A + t • B)⁻¹ ^ (n - i + 1) * B *
          (A + t • B)⁻¹ ^ (i + 1) * B)) t := by
  have hline : HasDerivAt (fun x : ℝ => A + x • B) B t := by
    simpa using ((hasDerivAt_id t).smul_const B).const_add A
  simpa only [Matrix.mul_zero, Matrix.trace_zero, add_zero] using
    hasDerivAt_matrix_trace_inv_pow_mul hline (hasDerivAt_const t B) hunit n

/-- Exact second derivative of an inverse trace power along an affine
matrix line, expressed without differentiating eigenvectors.
Source: inverse derivative and trace cyclicity; atlas
`wishart-lambda-min-tail` (operator calculus helper). -/
theorem hasDerivAt_matrix_trace_inv_pow_first (A B : Matrix ι ι ℝ)
    (n : ℕ) (t : ℝ) (hunit : IsUnit (A + t • B)) :
    HasDerivAt (fun x => -(n : ℝ) * Matrix.trace ((A + x • B)⁻¹ ^ (n + 1) * B))
      ((n : ℝ) * ∑ i ∈ Finset.range (n + 1),
        Matrix.trace ((A + t • B)⁻¹ ^ (n - i + 1) * B *
          (A + t • B)⁻¹ ^ (i + 1) * B)) t := by
  simpa only [neg_mul, mul_neg, neg_neg] using
    (hasDerivAt_matrix_trace_inv_pow_mul_const A B n t hunit).const_mul (-(n : ℝ))

end NLAlib
