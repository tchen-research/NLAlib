import NLAlib.Matrix.TraceYoung
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Polynomial traces of matrix series

Continuity, polynomial growth and coordinate derivatives for finite real
coefficient series of complex matrices. These are deterministic prerequisites
for the Gaussian Stein proof of integer noncommutative Khintchine moments.
Source: operator manuscript `eq:recursion`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open Matrix
namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Real part of complex matrix trace as a continuous real-linear map.
Source: trace linearity; supports `noncommutative-khintchine`. -/
def reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap ι ℝ ℂ).toContinuousLinearMap

omit [DecidableEq ι] in
/-- The continuous trace map computes the usual real trace.
Source: trace linearity; supports `noncommutative-khintchine`. -/
@[simp] theorem reTraceCLM_apply (M : Matrix ι ι ℂ) :
    reTraceCLM M = M.trace.re := rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- A finite real-coefficient Hermitian series remains Hermitian.
Source: linearity of the adjoint; supports `noncommutative-khintchine`. -/
theorem isHermitian_sum_smul_real (A : κ → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x : κ → ℝ) :
    (∑ i, x i • A i).IsHermitian := by
  apply isSelfAdjoint_sum
  intro i _
  exact (hA i).smul (isSelfAdjoint_iff.mpr (by simp))

omit [DecidableEq κ] in
/-- The matrix variance `∑ Aᵢ²` of Hermitian coefficients is PSD.
Source: the Gram identity; supports `noncommutative-khintchine`. -/
theorem posSemidef_sum_sq_of_isHermitian (A : κ → Matrix ι ι ℂ)
    (hA : ∀ i, (A i).IsHermitian) : (∑ i, A i ^ 2).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [(hA i).eq, pow_two] using Matrix.posSemidef_conjTranspose_mul_self (A i)

omit [DecidableEq κ] in
/-- A finite matrix series is bounded explicitly by a linear polynomial
in its real coefficient-vector norm. Source: triangle inequality;
supports `noncommutative-khintchine`. -/
theorem norm_sum_smul_le_sum_norm_mul_one_add_norm
    (A : κ → Matrix ι ι ℂ) (x : κ → ℝ) :
    ‖∑ i, x i • A i‖ ≤ (∑ i, ‖A i‖) * (1 + ‖x‖) := by
  calc _ ≤ ∑ i, ‖x i • A i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖A i‖ * (1 + ‖x‖) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have h := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at h
      linarith
    _ = _ := by rw [Finset.sum_mul]

omit [DecidableEq κ] in
/-- Matrix-series polynomial traces are continuous scalar functions.
Source: finite sums, matrix products and continuous trace;
supports `noncommutative-khintchine`. -/
theorem continuous_re_trace_series_product
    (A : κ → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) (r s : ℕ) :
    Continuous (fun x : κ → ℝ =>
      (B * (∑ i, x i • A i) ^ r * C * (∑ i, x i • A i) ^ s).trace.re) := by
  change Continuous (fun x : κ → ℝ => reTraceCLM
    (B * (∑ i, x i • A i) ^ r * C * (∑ i, x i • A i) ^ s))
  apply reTraceCLM.continuous.comp
  fun_prop

omit [DecidableEq κ] in
/-- Polynomial traces of matrix series have an explicit polynomial-growth
majorant. Source: submultiplicativity and continuous trace;
supports Gaussian integrability for `noncommutative-khintchine`. -/
theorem abs_re_trace_series_product_le
    (A : κ → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) (r s : ℕ) (x : κ → ℝ) :
    |(B * (∑ i, x i • A i) ^ r * C * (∑ i, x i • A i) ^ s).trace.re| ≤
      (‖(reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)‖ * ‖B‖ * ‖C‖ *
        (∑ i, ‖A i‖) ^ (r + s)) * (1 + ‖x‖) ^ (r + s) := by
  let Y := ∑ i, x i • A i
  classical
  have hpower (M : Matrix ι ι ℂ) (k : ℕ) : ‖M ^ k‖ ≤ ‖M‖ ^ k := by
    cases k with
    | zero =>
      simp only [pow_zero]
      rw [Matrix.cstar_norm_def, map_one]
      exact ContinuousLinearMap.norm_id_le
    | succ k => exact norm_pow_le' M (Nat.succ_pos k)
  have hnorm := norm_sum_smul_le_sum_norm_mul_one_add_norm A x
  have htrace := reTraceCLM.le_opNorm (B * Y ^ r * C * Y ^ s)
  rw [reTraceCLM_apply, Real.norm_eq_abs] at htrace
  calc _ ≤ ‖(reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)‖ * ‖B * Y ^ r * C * Y ^ s‖ := htrace
    _ ≤ ‖(reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)‖ *
        (‖B‖ * ‖Y‖ ^ r * ‖C‖ * ‖Y‖ ^ s) := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hpower _ _) (norm_nonneg _)))
          (norm_nonneg _))) (hpower _ _) (norm_nonneg _) (by positivity))
    _ ≤ ‖(reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)‖ *
        (‖B‖ * ((∑ i, ‖A i‖) * (1 + ‖x‖)) ^ r * ‖C‖ *
          ((∑ i, ‖A i‖) * (1 + ‖x‖)) ^ s) := by gcongr
    _ = _ := by rw [mul_pow, mul_pow, pow_add, pow_add]; ring

/-- Replacing one real coefficient differentiates a finite matrix series
by its coefficient matrix. Source: the polynomial product rule in manuscript
`eq:recursion`; supports `noncommutative-khintchine`. -/
theorem hasDerivAt_sum_smul_update
    (A : κ → Matrix ι ι ℂ) (x : κ → ℝ) (i : κ) (t : ℝ) :
    HasDerivAt (fun y => ∑ j, Function.update x i y j • A j) (A i) t := by
  let L : (κ → ℝ) →L[ℝ] Matrix ι ι ℂ :=
    ∑ j, (ContinuousLinearMap.proj j).smulRight (A j)
  have h := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)
  convert! h using 1
  · funext y
    simp only [Function.comp_apply, L, _root_.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  · simp [L, Pi.single_apply]

/-- Coordinate derivative of a coefficient times a matrix-series power,
followed by real trace. Source: the noncommutative product rule in manuscript
`eq:recursion`; supports `noncommutative-khintchine`. -/
theorem hasDerivAt_re_trace_mul_series_pow_update
    (A : κ → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (x : κ → ℝ)
    (i : κ) (t : ℝ) (q : ℕ) :
    HasDerivAt
      (fun y => (B * (∑ j, Function.update x i y j • A j) ^ q).trace.re)
      (∑ l ∈ Finset.range q,
        (B * (∑ j, Function.update x i t j • A j) ^ (q.pred - l) *
          A i * (∑ j, Function.update x i t j • A j) ^ l).trace.re) t := by
  have hp := (hasDerivAt_sum_smul_update A x i t).fun_pow' q
  have hmul := (hasDerivAt_const t B).mul hp
  have htrace := (hasDerivAt_const t
    (reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)).clm_apply hmul
  convert! htrace using 1
  · simp only [_root_.zero_apply, zero_mul, zero_add, reTraceCLM_apply, Finset.mul_sum,
      Matrix.trace_sum, Complex.re_sum, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
/-- A single sign flip changes a finite matrix series by twice its signed
coefficient. Source: manuscript individual sign-flip identity; supports
`noncommutative-khintchine`. -/
theorem sum_smul_sub_sum_smul_update_neg
    (A : κ → Matrix ι ι ℂ) (x : κ → ℝ) (i : κ) :
    (∑ j, x j • A j) - (∑ j, Function.update x i (-x i) j • A j) =
      (2 * x i) • A i := by
  rw [← Finset.sum_sub_distrib]
  have hpoint (j : κ) : x j • A j - Function.update x i (-x i) j • A j =
      if j = i then (2 * x i) • A i else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self, if_true, ← sub_smul]
      congr 1
      ring
    · simp only [Function.update_of_ne hji, hji, if_false, sub_self]
  simp_rw [hpoint]
  simp

end NLAlib
