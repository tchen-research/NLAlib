import NLAlib.Gaussian.SeriesPolynomialMoments
import NLAlib.Concentration.Matrix.Series.PolynomialMoment

/-!
# Integer noncommutative Khintchine: Gaussian coefficients

The exact standard Gaussian product law, coordinate Stein and the mixed-power
trace inequality give the lower-moment recursion. Polynomial trace Young then
closes the moment with constant `(2p-1)^p`, without dividing by a moment.
Source: operator manuscript `eq:recursion`, `thm:khintchine`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The exact Gaussian matrix-series moment obeys the polynomial lower-moment
recursion at every odd exponent. Source: manuscript `eq:recursion`, derived by
coordinate Stein and mixed traces; supports `noncommutative-khintchine`. -/
theorem integral_re_trace_gaussianSeries_even_pow_le_recursion
    (A : Fin n → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ x : Fin n → ℝ, ((∑ i, x i • A i) ^ (2 * p)).trace.re
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2 * p - 1 : ℕ) *
        ∫ x : Fin n → ℝ,
          ((∑ i, A i ^ 2) * (∑ j, x j • A j) ^ (2 * p - 2)).trace.re
          ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let γ := Measure.pi fun _ : Fin n => gaussianReal 0 1
  let Y := fun x : Fin n → ℝ => ∑ i, x i • A i
  let q := 2 * p - 1
  let m := 2 * p - 2
  have hqm : q.pred = m := by dsimp [q, m]; omega
  have hpow : 2 * p = q + 1 := by dsimp [q]; omega
  have hm : Even m := by
    have he : m = 2 * (p - 1) := by dsimp [m]; omega
    rw [he]
    exact even_two_mul _
  have hYi (x) : (Y x).IsHermitian := isHermitian_sum_smul_real A hA x
  have hexpand (x : Fin n → ℝ) : (Y x ^ (2 * p)).trace.re =
      ∑ i, x i * (A i * Y x ^ q).trace.re := by
    rw [hpow, pow_succ', show Y x = ∑ i, x i • A i by rfl,
      Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  have hcoord (i : Fin n) :
      (∫ x, x i * (A i * Y x ^ q).trace.re ∂γ) ≤
        (q : ℝ) * ∫ x, (A i ^ 2 * Y x ^ m).trace.re ∂γ := by
    rw [integral_coordinate_mul_re_trace_mul_gaussianSeries_pow]
    have hbound (l : ℕ) (hl : l ∈ Finset.range q) :
        (∫ x : Fin n → ℝ,
          (A i * Y x ^ (q.pred - l) * A i * Y x ^ l).trace.re ∂γ) ≤
        ∫ x : Fin n → ℝ, (A i ^ 2 * Y x ^ m).trace.re ∂γ := by
      apply integral_mono
        (integrable_re_trace_gaussianSeries_product A (A i) (A i) (q.pred - l) l)
        (integrable_re_trace_mul_gaussianSeries_pow A (A i ^ 2) m)
      intro x
      have hlm : l ≤ m := by dsimp [q, m] at *; rw [Finset.mem_range] at hl; omega
      have h := re_trace_mul_pow_mul_le_trace_sq_mul_pow (A i) (Y x)
        (hA i) (hYi x) hm (Nat.sub_le m l)
      simpa only [hqm, Nat.sub_sub_self hlm] using h
    calc _ ≤ ∑ _l ∈ Finset.range q,
          ∫ x : Fin n → ℝ, (A i ^ 2 * Y x ^ m).trace.re ∂γ :=
        Finset.sum_le_sum hbound
      _ = _ := by simp
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hcoord i
  have hM : (∫ x, (Y x ^ (2 * p)).trace.re ∂γ) =
      ∑ i, ∫ x, x i * (A i * Y x ^ q).trace.re ∂γ := by
    simp_rw [hexpand]
    exact integral_finsetSum _ fun i _ =>
      integrable_coordinate_mul_re_trace_mul_gaussianSeries_pow A (A i) q i
  have hW : (∫ x, ((∑ i, A i ^ 2) * Y x ^ m).trace.re ∂γ) =
      ∑ i, ∫ x, (A i ^ 2 * Y x ^ m).trace.re ∂γ := by
    simp_rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    exact integral_finsetSum _ fun i _ => integrable_re_trace_mul_gaussianSeries_pow A (A i ^ 2) m
  rw [hM, hW]
  simpa only [Finset.mul_sum] using hsum

/-- **Integer noncommutative Khintchine, Gaussian polynomial form.** For the
actual standard Gaussian coefficients and fixed complex Hermitian matrices,
the `2p` trace moment is at most `(2p-1)^p tr((∑ Aᵢ²)^p)`. Empty coefficient
families, empty matrices and zero variance are included. Source: manuscript
`thm:khintchine`, Gaussian branch.
atlas: noncommutative-khintchine (partial) -/
theorem integral_re_trace_gaussianSeries_pow_le
    (A : Fin n → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ x : Fin n → ℝ, ((∑ i, x i • A i) ^ (2 * p)).trace.re
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2 * p - 1 : ℕ) ^ p * ((∑ i, A i ^ 2) ^ p).trace.re := by
  apply integral_re_trace_pow_le_of_polynomial_recursion
    (∑ i, A i ^ 2) (posSemidef_sum_sq_of_isHermitian A hA)
    (fun x : Fin n → ℝ => ∑ i, x i • A i)
    (ae_of_all _ (isHermitian_sum_smul_real A hA)) hp
  · simpa only [one_mul] using integrable_re_trace_mul_gaussianSeries_pow A 1 (2 * p)
  · exact integrable_re_trace_mul_gaussianSeries_pow A (∑ i, A i ^ 2) (2 * p - 2)
  · exact integral_re_trace_gaussianSeries_even_pow_le_recursion A hA hp

end NLAlib
