import NLAlib.Probability.Gaussian.Moments.SeriesPolynomialMoments
import NLAlib.Matrix.Norms.HermitianEvenTrace
import NLAlib.ForMathlib.MeasureTheory.MomentInterpolation

/-! # Gaussian series norm moments and the trace method

Finite Gaussian series have every natural spectral-norm moment. Scalar
probability-space moment comparison and the Hermitian spectral theorem bound
the actual expected norm by any positive even trace moment.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- Every finite complex Gaussian matrix series has all natural moments of
its named spectral norm, with no integrability assumptions on the statement. -/
theorem integrable_specNorm_gaussianSeries_pow (A : ι → Matrix d d ℂ) (q : ℕ) :
    Integrable (fun x : ι → ℝ => specNorm (∑ i, x i • A i) ^ q) (gaussianVector ι) := by
  have hcont : Continuous (fun x : ι → ℝ => specNorm (∑ i, x i • A i) ^ q) := by
    simp only [specNorm_eq_norm]
    fun_prop
  apply integrable_gaussianVector_of_polynomial_growth hcont.measurable.aemeasurable
    ((∑ i, specNorm (A i)) ^ q) q
  intro x
  rw [abs_of_nonneg (pow_nonneg (specNorm_nonneg _) _)]
  have hh := pow_le_pow_left₀ (norm_nonneg (∑ i, x i • A i))
    (norm_sum_smul_le_sum_norm_mul_one_add_norm A x) q
  simpa only [specNorm_eq_norm, mul_pow] using hh

open scoped Matrix.Norms.L2Operator in
/-- The actual expectation of the spectral norm of a Hermitian Gaussian
series is at most every positive even trace moment root. -/
theorem integral_specNorm_gaussianSeries_le_even_trace_rpow
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) {p : ℕ} (hp : 1 ≤ p) :
    (∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι) ≤
      (∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι) ^
        (1 / (2 * (p : ℝ))) := by
  let f : (ι → ℝ) → ℝ := fun x => specNorm (∑ i, x i • A i)
  have hf : Continuous f := by
    dsimp [f]
    simp only [specNorm_eq_norm]
    fun_prop
  have hn : ∀ x, 0 ≤ f x := fun x => specNorm_nonneg _
  have hpower := integrable_specNorm_gaussianSeries_pow A (2 * p)
  have hpowR : Integrable (fun x => f x ^ (2 * (p : ℝ))) (gaussianVector ι) := by
    simpa only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, f] using hpower
  have hroot := integral_rpow_root_le_of_nonneg_of_le hf.aestronglyMeasurable hn
    (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) ≤ 2 * p by exact_mod_cast (by omega : 1 ≤ 2 * p)) hpowR
  simp only [Real.rpow_one, inv_one, one_div] at hroot
  have htrace : Integrable (fun x : ι → ℝ => ((∑ i, x i • A i) ^ (2 * p)).trace.re)
      (gaussianVector ι) := by
    simpa only [one_mul] using integrable_re_trace_mul_gaussianSeries_pow A 1 (2 * p)
  have hint : (∫ x, f x ^ (2 * (p : ℝ)) ∂gaussianVector ι) ≤
      ∫ x, ((∑ i, x i • A i) ^ (2 * p)).trace.re ∂gaussianVector ι := by
    apply integral_mono hpowR htrace
    intro x
    have hh := specNorm_pow_two_mul_le_re_trace_pow (isHermitian_sum_smul_real A hA x)
      (show 0 < p by omega)
    simpa only [f, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat] using hh
  exact hroot.trans (by
    simpa only [one_div] using Real.rpow_le_rpow
      (integral_nonneg (fun x => Real.rpow_nonneg (hn x) _)) hint
      (show 0 ≤ (2 * (p : ℝ))⁻¹ by positivity))

end NLAlib
