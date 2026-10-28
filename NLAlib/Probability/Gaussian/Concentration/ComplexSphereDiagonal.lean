import NLAlib.Probability.Gaussian.Basic.ComplexSphere
import NLAlib.Probability.Gaussian.Moments.ComplexExponentialSquare
import NLAlib.ForMathlib.Analysis.LogAffineMean
import Mathlib.Probability.Moments.Basic

/-!
# Native complex-sphere concentration for bounded diagonal forms

The normalized circular Gaussian law is used directly. An exact Gaussian
Laplace transform and finite log concavity give a dimension-dependent tail.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
namespace NLAlib
variable {n : Type*} [Fintype n]

/-- The real diagonal quadratic form of a complex vector. -/
def sphereDiagonalForm (d : n → ℝ) (b : n → ℂ) : ℝ :=
  ∑ i, d i * Complex.normSq (b i)

private theorem normSq_complexVector (z : n → ℂ) :
    ‖WithLp.toLp 2 z‖^2 = ∑ i, Complex.normSq (z i) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Complex.normSq_eq_norm_sq]

/-- Radial normalization divides the diagonal quadratic form by the squared norm. -/
theorem sphereDiagonalForm_normalize (d : n → ℝ) (z : n → ℂ) :
    sphereDiagonalForm d (normalizeComplexVector z) =
      sphereDiagonalForm d z / ‖WithLp.toLp 2 z‖^2 := by
  unfold sphereDiagonalForm
  simp only [normalizeComplexVector, Pi.smul_apply, Complex.normSq_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact upper-tail Chernoff estimate for the unnormalized comparison form. -/
theorem measureReal_sum_sub_mul_normSq_nonneg_le
    (d : n → ℝ) {m x : ℝ} (hm : -1 < m) (hm1 : m < 1)
    (hmx : m < x) (hx : x < 1) (hd : ∀ i, d i ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∑ i, d i = Fintype.card n * m) :
    (circularComplexGaussianVector n).real
      {z | 0 ≤ ∑ i, (d i-x)*Complex.normSq (z i)} ≤
      exp (-(Fintype.card n : ℝ)*(x-m)^2/2) := by
  let t := sphereChernoffParameter m x
  have ht : 0 < t := by
    have hxm : -1 < x := hm.trans hmx
    have hden : 0 < 1-x^2 := by nlinarith
    dsimp [t,sphereChernoffParameter]
    positivity
  have hi i : t*(d i-x) < 1/2 :=
    sphereChernoffParameter_mul_sub_lt_half hm hmx hx (hd i).2
  have hint : Integrable (fun z : n → ℂ => exp (t*∑ i, (d i-x)*Complex.normSq (z i)))
      (circularComplexGaussianVector n) := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    exact integrable_exp_sum_mul_normSq_circularComplexGaussianVector _ hi
  have hc := measure_ge_le_exp_mul_mgf
    (μ := circularComplexGaussianVector n)
    (X := fun z : n → ℂ => ∑ i, (d i-x)*Complex.normSq (z i)) 0 ht.le hint
  simp only [mul_zero, exp_zero, one_mul, mgf] at hc
  have he : (∫ z : n → ℂ, exp (t*∑ i, (d i-x)*Complex.normSq (z i))
      ∂circularComplexGaussianVector n) =
      exp (-(∑ i, log (1-2*t*(d i-x)))) := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [integral_exp_sum_mul_normSq_circularComplexGaussianVector _ hi,
      exp_neg, exp_sum]
    simp_rw [show ∀ i, exp (log (1-2*t*(d i-x))) = 1-2*t*(d i-x) from
      fun i => exp_log (by linarith [hi i])]
    simp only [mul_assoc]
    rw [Finset.prod_inv_distrib]
  apply hc.trans
  rw [he]
  apply exp_le_exp.mpr
  have hlog := card_mul_sub_sq_div_two_le_sum_log_affine d hm hm1 hmx hx hd hmean
  dsimp [t]
  linarith

/-- The native normalized law inherits the comparison estimate at every interior
upper-tail threshold. -/
theorem measureReal_sphereDiagonalForm_ge_le_of_interior
    (d : n → ℝ) {m x : ℝ} (hm : -1 < m) (hm1 : m < 1)
    (hmx : m < x) (hx : x < 1) (hd : ∀ i, d i ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∑ i, d i = Fintype.card n * m) :
    (complexSphereVector n).real {b | x ≤ sphereDiagonalForm d b} ≤
      exp (-(Fintype.card n : ℝ)*(x-m)^2/2) := by
  rw [← hasLaw_normalizeComplexVector_circularComplexGaussianVector.measureReal_eq
    (p := fun b : n → ℂ => x ≤ sphereDiagonalForm d b) (by
      unfold sphereDiagonalForm
      exact measurableSet_le measurable_const (by fun_prop))]
  apply le_trans (measureReal_mono ?_)
    (measureReal_sum_sub_mul_normSq_nonneg_le d hm hm1 hmx hx hd hmean)
  intro z hz
  change x ≤ sphereDiagonalForm d (normalizeComplexVector z) at hz
  change 0 ≤ ∑ i, (d i-x)*Complex.normSq (z i)
  by_cases he : z = 0
  · simp [he]
  have hn : ‖WithLp.toLp 2 z‖ ≠ 0 := by
    intro h
    exact he ((WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp h))
  rw [sphereDiagonalForm_normalize] at hz
  have hmul := (le_div_iff₀ (sq_pos_of_ne_zero hn)).mp hz
  rw [normSq_complexVector] at hmul
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  exact sub_nonneg.mpr hmul

/-- A bounded diagonal form is bounded by the squared Euclidean vector norm. -/
theorem sphereDiagonalForm_le_norm_sq (d : n → ℝ)
    (hd : ∀ i, d i ≤ 1) (b : n → ℂ) :
    sphereDiagonalForm d b ≤ ‖WithLp.toLp 2 b‖^2 := by
  rw [normSq_complexVector]
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_right (hd i) (Complex.normSq_nonneg (b i))).trans_eq (one_mul _)

/-- Constant diagonal forms are precisely a scalar times the squared vector norm. -/
theorem sphereDiagonalForm_const (c : ℝ) (b : n → ℂ) :
    sphereDiagonalForm (fun _ => c) b = c*‖WithLp.toLp 2 b‖^2 := by
  rw [sphereDiagonalForm, normSq_complexVector, Finset.mul_sum]

/-- One-sided native sphere concentration, including every endpoint mean and
every positive deviation size. -/
theorem measureReal_sphereDiagonalForm_sub_mean_gt_le [Nonempty n]
    (d : n → ℝ) {m r : ℝ} (hm : m ∈ Set.Icc (-1 : ℝ) 1) (hr : 0 < r)
    (hd : ∀ i, d i ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∑ i, d i = Fintype.card n * m) :
    (complexSphereVector n).real {b | r < sphereDiagonalForm d b-m} ≤
      exp (-(Fintype.card n : ℝ)*r^2/2) := by
  by_cases hx : m+r < 1
  · by_cases hm0 : m = -1
    · have hzero : ∑ i, (d i+1) = 0 := by
        rw [Finset.sum_add_distrib, hmean, hm0]
        simp
      have he (i : n) : d i = -1 := by
        have h := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ Finset.univ) => by linarith [(hd j).1])).mp hzero i (mem_univ i)
        linarith
      have hde : d = fun _ => -1 := funext he
      have hz : (complexSphereVector n) {b | r < sphereDiagonalForm d b-m} = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [ae_norm_eq_one_complexSphereVector (n := n)] with b hb
        rw [hde,sphereDiagonalForm_const,hb,hm0]
        simpa using hr.le
      simp only [Measure.real, hz, ENNReal.toReal_zero]
      exact (exp_pos _).le
    · have hi := measureReal_sphereDiagonalForm_ge_le_of_interior d
        (lt_of_le_of_ne hm.1 (Ne.symm hm0)) (by linarith) (by linarith) hx hd hmean
      apply le_trans (measureReal_mono (fun b hb => by
        change r < sphereDiagonalForm d b-m at hb
        change m+r ≤ sphereDiagonalForm d b
        linarith))
        (hi.trans_eq (by congr 1; ring))
  · have hz : (complexSphereVector n) {b | r < sphereDiagonalForm d b-m} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ae_norm_eq_one_complexSphereVector (n := n)] with b hb
      have h := sphereDiagonalForm_le_norm_sq d (fun i => (hd i).2) b
      rw [hb] at h
      exact not_lt_of_ge (by linarith)
    simp only [Measure.real, hz, ENNReal.toReal_zero]
    exact (exp_pos _).le

/-- Two-sided concentration for actual complex unit-sphere quadratic forms.
The exponent is stronger than the sphere-Lipschitz estimate used in the atlas. -/
theorem measureReal_abs_sphereDiagonalForm_sub_mean_gt_le [Nonempty n]
    (d : n → ℝ) {m r : ℝ} (hm : m ∈ Set.Icc (-1 : ℝ) 1) (hr : 0 < r)
    (hd : ∀ i, d i ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∑ i, d i = Fintype.card n * m) :
    (complexSphereVector n).real {b | r < |sphereDiagonalForm d b-m|} ≤
      2*exp (-(Fintype.card n : ℝ)*r^2/2) := by
  have hp := measureReal_sphereDiagonalForm_sub_mean_gt_le d hm hr hd hmean
  have hmn : -m ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> linarith [hm.1,hm.2]
  have hdn i : -d i ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> linarith [(hd i).1,(hd i).2]
  have hmean' : ∑ i, -d i = Fintype.card n * -m := by rw [Finset.sum_neg_distrib,hmean];ring
  have hn := measureReal_sphereDiagonalForm_sub_mean_gt_le (fun i => -d i) hmn hr hdn hmean'
  have he : ∀ b, sphereDiagonalForm (fun i => -d i) b = -sphereDiagonalForm d b := by
    intro b
    simp [sphereDiagonalForm,neg_mul,Finset.sum_neg_distrib]
  have hsub : {b | r < |sphereDiagonalForm d b-m|} ⊆
      {b | r < sphereDiagonalForm d b-m} ∪
      {b | r < sphereDiagonalForm (fun i => -d i) b-(-m)} := by
    intro b hb
    change r < |sphereDiagonalForm d b-m| at hb
    rcases lt_abs.mp hb with h | h
    · exact Or.inl h
    · right
      change r < sphereDiagonalForm (fun i => -d i) b-(-m)
      rw [he]
      linarith
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by linarith))

end NLAlib
