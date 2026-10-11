import NLAlib.Concentration.Matrix.Series.RademacherPolynomialMoments
import NLAlib.Concentration.Matrix.Series.PolynomialMoment
import NLAlib.Matrix.TraceMeanValue

/-!
# Integer noncommutative Khintchine: Rademacher coefficients

Individual measure-preserving coordinate flips and the polynomial trace
mean-value inequality prove the exact lower-moment recursion on the actual
finite product Rademacher law. Polynomial trace Young closes the recursion.
Source: operator manuscript `eq:recursion`, `thm:khintchine`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A single coordinate sign flip gives the exact odd-power trace recursion
for that Hermitian coefficient. Source: manuscript Rademacher sign-flip
argument; supports `noncommutative-khintchine`. -/
theorem integral_coordinate_mul_re_trace_mul_rademacherSeries_pow_le
    (A : κ → Matrix ι ι ℂ) (hA : ∀ j, (A j).IsHermitian)
    (i : κ) {m : ℕ} (hm : Even m) :
    (∫ x : κ → ℝ, x i * (A i * (∑ j, x j • A j) ^ (m + 1)).trace.re
        ∂Measure.pi (fun _ => rademacherMeasure)) ≤
      (m + 1 : ℕ) *
        ∫ x : κ → ℝ, (A i ^ 2 * (∑ j, x j • A j) ^ m).trace.re
          ∂Measure.pi (fun _ => rademacherMeasure) := by
  let μ := Measure.pi fun _ : κ => rademacherMeasure
  let Y := fun x : κ → ℝ => ∑ j, x j • A j
  let T := fun x : κ → ℝ => Function.update x i (-x i)
  let f := fun x : κ → ℝ => x i * (A i * Y x ^ (m + 1)).trace.re
  let g := fun x : κ → ℝ => (A i ^ 2 * Y x ^ m).trace.re
  have hf : Continuous f := by
    have h := (continuous_apply i).mul
      (continuous_re_trace_series_product A (A i) 1 (m + 1) 0)
    have he : ((fun x : κ → ℝ => x i) * fun x =>
        (A i * (∑ j, x j • A j) ^ (m + 1) * 1 * (∑ j, x j • A j) ^ 0).trace.re) = f := by
      funext x
      simp only [Pi.mul_apply, pow_zero, mul_one]
      rfl
    rw [he] at h
    exact h
  have hg : Continuous g := by
    simpa only [pow_zero, mul_one] using
      continuous_re_trace_series_product A (A i ^ 2) 1 m 0
  have hfi : Integrable f μ :=
    integrable_coordinate_mul_re_trace_mul_rademacherSeries_pow A (A i) (m + 1) i
  have hgi : Integrable g μ := integrable_re_trace_mul_rademacherSeries_pow A (A i ^ 2) m
  have hmp := measurePreserving_update_neg_pi_rademacherMeasure i
  have hTfi : Integrable (fun x => f (T x)) μ := hmp.integrable_comp_of_integrable hfi
  have hTgi : Integrable (fun x => g (T x)) μ := hmp.integrable_comp_of_integrable hgi
  have hYi (x) : (Y x).IsHermitian := isHermitian_sum_smul_real A hA x
  have hD (x) : Y x - Y (T x) = (2 * x i) • A i :=
    sum_smul_sub_sum_smul_update_neg A x i
  have hpoint : ∀ᵐ x ∂μ,
      2 * (f x + f (T x)) ≤ 2 * (m + 1 : ℕ) * (g x + g (T x)) := by
    have hsign : ∀ᵐ x : κ → ℝ ∂μ, x i = 1 ∨ x i = -1 :=
      (Measure.tendsto_eval_ae_ae (μ := fun _ : κ => rademacherMeasure) (i := i)).eventually
        ae_eq_one_or_neg_one_rademacherMeasure
    filter_upwards [hsign] with x hx
    have hxi : x i ^ 2 = 1 := by rcases hx with h | h <;> simp [h]
    have hmean := re_trace_sub_mul_sub_pow_le (Y x) (Y (T x)) (hYi x) (hYi (T x)) hm
    rw [hD] at hmean
    have hsq : ((2 * x i) • A i) ^ 2 = (4 : ℝ) • A i ^ 2 := by
      rw [smul_pow, mul_pow, hxi, mul_one]
      norm_num
    rw [hsq] at hmean
    have hleft : (((2 * x i) • A i) *
        (Y x ^ (m + 1) - Y (T x) ^ (m + 1))).trace.re =
        2 * (f x + f (T x)) := by
      simp only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
        mul_sub, Matrix.trace_sub, Complex.sub_re, f, T, Function.update_self]
      ring
    have hright : ((4 : ℝ) • A i ^ 2 * (Y x ^ m + Y (T x) ^ m)).trace.re =
        4 * (g x + g (T x)) := by
      simp only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
        mul_add, Matrix.trace_add, Complex.add_re, g]
    rw [hleft, hright] at hmean
    nlinarith [hmean]
  have hi := integral_mono_ae ((hfi.add hTfi).const_mul 2)
    ((hgi.add hTgi).const_mul (2 * (m + 1 : ℕ))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_const_mul, integral_add hfi hTfi,
    integral_add hgi hTgi, integral_update_neg_pi_rademacherMeasure i f hf.measurable,
    integral_update_neg_pi_rademacherMeasure i g hg.measurable] at hi
  linarith

/-- The exact Rademacher matrix-series even moment obeys the polynomial
lower-moment recursion. Source: individual sign flips in manuscript
`eq:recursion`; supports `noncommutative-khintchine`. -/
theorem integral_re_trace_rademacherSeries_even_pow_le_recursion
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ x : κ → ℝ, ((∑ i, x i • A i) ^ (2 * p)).trace.re
        ∂Measure.pi (fun _ => rademacherMeasure)) ≤
      (2 * p - 1 : ℕ) *
        ∫ x : κ → ℝ,
          ((∑ i, A i ^ 2) * (∑ j, x j • A j) ^ (2 * p - 2)).trace.re
          ∂Measure.pi (fun _ => rademacherMeasure) := by
  let μ := Measure.pi fun _ : κ => rademacherMeasure
  let Y := fun x : κ → ℝ => ∑ i, x i • A i
  let q := 2 * p - 1
  let m := 2 * p - 2
  have hmq : m + 1 = q := by dsimp [m, q]; omega
  have hpow : 2 * p = q + 1 := by dsimp [q]; omega
  have hm : Even m := by
    have he : m = 2 * (p - 1) := by dsimp [m]; omega
    rw [he]
    exact even_two_mul _
  have hexpand (x : κ → ℝ) : (Y x ^ (2 * p)).trace.re =
      ∑ i, x i * (A i * Y x ^ q).trace.re := by
    rw [hpow, pow_succ', show Y x = ∑ i, x i • A i by rfl,
      Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  have hcoord (i : κ) := integral_coordinate_mul_re_trace_mul_rademacherSeries_pow_le A hA i hm
  rw [hmq] at hcoord
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset κ)) => hcoord i
  have hM : (∫ x, (Y x ^ (2 * p)).trace.re ∂μ) =
      ∑ i, ∫ x, x i * (A i * Y x ^ q).trace.re ∂μ := by
    simp_rw [hexpand]
    exact integral_finsetSum _ fun i _ =>
      integrable_coordinate_mul_re_trace_mul_rademacherSeries_pow A (A i) q i
  have hW : (∫ x, ((∑ i, A i ^ 2) * Y x ^ m).trace.re ∂μ) =
      ∑ i, ∫ x, (A i ^ 2 * Y x ^ m).trace.re ∂μ := by
    simp_rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    exact integral_finsetSum _ fun i _ => integrable_re_trace_mul_rademacherSeries_pow A (A i ^ 2) m
  rw [hM, hW]
  simpa only [Finset.mul_sum] using hsum

/-- **Integer noncommutative Khintchine, Rademacher polynomial form.** Fixed
complex Hermitian coefficient matrices under the actual product sign law
obey the exact `(2p-1)^p` trace-moment bound. Source: manuscript
`thm:khintchine`, Rademacher branch. Empty coefficient and matrix types and
zero variance are included.
atlas: noncommutative-khintchine (partial) -/
theorem integral_re_trace_rademacherSeries_pow_le
    (A : κ → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ x : κ → ℝ, ((∑ i, x i • A i) ^ (2 * p)).trace.re
        ∂Measure.pi (fun _ => rademacherMeasure)) ≤
      (2 * p - 1 : ℕ) ^ p * ((∑ i, A i ^ 2) ^ p).trace.re := by
  apply integral_re_trace_pow_le_of_polynomial_recursion
    (∑ i, A i ^ 2) (posSemidef_sum_sq_of_isHermitian A hA)
    (fun x : κ → ℝ => ∑ i, x i • A i)
    (ae_of_all _ (isHermitian_sum_smul_real A hA)) hp
  · simpa only [one_mul] using integrable_re_trace_mul_rademacherSeries_pow A 1 (2 * p)
  · exact integrable_re_trace_mul_rademacherSeries_pow A (∑ i, A i ^ 2) (2 * p - 2)
  · exact integral_re_trace_rademacherSeries_even_pow_le_recursion A hA hp

end NLAlib
