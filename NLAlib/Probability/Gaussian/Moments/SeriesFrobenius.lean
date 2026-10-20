import NLAlib.Probability.Gaussian.Moments.ComplexLinearMoments
import NLAlib.Matrix.Norms.BilinearProbes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith

/-! # Exact Gaussian coefficient Frobenius moments and localization

All expectations use the actual independent standard Gaussian coefficient law.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

private theorem complexGaussianLinearForm_star (a : ι → ℂ) (x : ι → ℝ) :
    complexGaussianLinearForm (fun i => star (a i)) x = star (complexGaussianLinearForm a x) := by
  classical
  simp only [complexGaussianLinearForm, map_sum, map_mul, Complex.star_def,
    Complex.conj_ofReal]

/-- The exact second absolute moment of an actual complex linear form of real
standard Gaussian coordinates is its coefficient square sum. -/
theorem integral_norm_sq_complexGaussianLinearForm (a : ι → ℂ) :
    (∫ x : ι → ℝ, ‖complexGaussianLinearForm a x‖^2 ∂gaussianVector ι) = ∑ i, ‖a i‖^2 := by
  classical
  have he (x : ι → ℝ) : ‖complexGaussianLinearForm a x‖^2 =
      (complexGaussianLinearForm (fun i => star (a i)) x * complexGaussianLinearForm a x).re := by
    rw [complexGaussianLinearForm_star]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
    ring
  simp_rw [he]
  have hRe := integral_re (integrable_complexGaussianLinearForm_mul (fun i => star (a i)) a)
  simp only [RCLike.re_eq_complex_re] at hRe
  rw [hRe, integral_complexGaussianLinearForm_mul]
  simp only [dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The actual squared norm of a complex Gaussian coefficient linear form
is integrable, including empty coefficient families. -/
theorem integrable_norm_sq_complexGaussianLinearForm (a : ι → ℂ) :
    Integrable (fun x : ι → ℝ => ‖complexGaussianLinearForm a x‖^2) (gaussianVector ι) := by
  have hh := (integrable_complexGaussianLinearForm_mul (fun i => star (a i)) a).re
  convert hh using 1
  funext x
  rw [complexGaussianLinearForm_star]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply, RCLike.re_eq_complex_re]
  ring

omit [DecidableEq d] in
/-- The exact expected Frobenius norm squared of an actual Gaussian matrix
series is the sum of its coefficient Frobenius norms squared. -/
theorem integral_frobSq_gaussianSeries_eq_sum (A : ι → Matrix d d ℂ) :
    (∫ x : ι → ℝ, frobSq (∑ i, x i • A i) ∂gaussianVector ι) = ∑ i, frobSq (A i) := by
  classical
  have he (x : ι → ℝ) (j k : d) : (∑ i, x i • A i) j k =
      complexGaussianLinearForm (fun i => A i j k) x := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
      complexGaussianLinearForm]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp only [frobSq_eq_sum_norm_sq, he]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    integrable_norm_sq_complexGaussianLinearForm (fun i => A i j k)))]
  simp_rw [integral_finsetSum _ (fun k _ =>
    integrable_norm_sq_complexGaussianLinearForm (fun i => A i _ k)),
    integral_norm_sq_complexGaussianLinearForm]
  calc
    _ = ∑ j : d, ∑ i : ι, ∑ k : d, ‖A i j k‖^2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

omit [DecidableEq d] in
/-- The actual squared Frobenius norm of a finite Gaussian matrix series is
integrable in arbitrary finite shape. -/
theorem integrable_frobSq_gaussianSeries (A : ι → Matrix d d ℂ) :
    Integrable (fun x : ι → ℝ => frobSq (∑ i, x i • A i)) (gaussianVector ι) := by
  classical
  have he (x : ι → ℝ) (j k : d) : (∑ i, x i • A i) j k =
      complexGaussianLinearForm (fun i => A i j k) x := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, complexGaussianLinearForm]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  simpa only [frobSq_eq_sum_norm_sq, he] using
    integrable_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ
      (fun k _ => integrable_norm_sq_complexGaussianLinearForm (fun i => A i j k)))

/-- Coordinate unit probes bound the actual expected squared Frobenius norm
by dimension squared times the actual bilinear variance. -/
theorem integral_frobSq_gaussianSeries_le_card_sq_bilinearSquareMass
    (A : ι → Matrix d d ℂ) :
    (∫ x : ι → ℝ, frobSq (∑ i, x i • A i) ∂gaussianVector ι) ≤
      (Fintype.card d : ℝ)^2 * bilinearSquareMass A Finset.univ := by
  classical
  rw [integral_frobSq_gaussianSeries_eq_sum]
  simp only [frobSq_eq_sum_norm_sq]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j : d, ∑ k : d, ∑ i : ι, ‖A i j k‖^2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ ≤ ∑ _j : d, ∑ _k : d, bilinearSquareMass A Finset.univ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      let e (j : d) : EuclideanSpace ℂ d := EuclideanSpace.single j 1
      have heval (B : Matrix d d ℂ) : star (e j).ofLp ⬝ᵥ (B *ᵥ (e k).ofLp) = B j k := by simp [e]
      simpa only [heval] using sum_bilinear_sq_le_bilinearSquareMass A Finset.univ
        (e j) (e k) (by simp [e]) (by simp [e])
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

open scoped Matrix.Norms.L2Operator in
/-- The actual Gaussian series is localized in a deterministic spectral norm
ball with a second-moment tail at the literal bilinear variance scale.
Source: second-moment Markov inequality; the fixed-confidence localization
step for arXiv:2406.11453v2, Theorem 2.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem measureReal_specNorm_gaussianSeries_gt_bilinear_scale_le [Nonempty d]
    (A : ι → Matrix d d ℂ) (hmass : 0 < bilinearSquareMass A Finset.univ)
    {q : ℝ} (hq : 0 < q) :
    (gaussianVector ι).real {x : ι → ℝ |
      4*(Fintype.card d : ℝ)*Real.sqrt (bilinearSquareMass A Finset.univ)*Real.sqrt q <
        specNorm (∑ i, x i • A i)} ≤ 1/(16*q) := by
  classical
  let L := 4*(Fintype.card d : ℝ)*Real.sqrt (bilinearSquareMass A Finset.univ)*Real.sqrt q
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
  have hL : 0 < L := by dsimp only [L]; positivity
  have hLsq : L^2 = 16*(Fintype.card d : ℝ)^2*bilinearSquareMass A Finset.univ*q := by
    dsimp only [L]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hmass.le, Real.sq_sqrt hq.le]
    ring
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x : ι → ℝ => frobSq_nonneg (∑ i, x i • A i))
    (integrable_frobSq_gaussianSeries A) (L^2)
  have hsub : {x : ι → ℝ | L < specNorm (∑ i, x i • A i)} ⊆
      {x : ι → ℝ | L^2 ≤ frobSq (∑ i, x i • A i)} := by
    intro x hx
    exact (pow_le_pow_left₀ hL.le hx.le 2).trans (specNorm_sq_le_frobSq _)
  calc
    _ ≤ (gaussianVector ι).real {x : ι → ℝ | L^2 ≤ frobSq (∑ i, x i • A i)} :=
      measureReal_mono hsub
    _ ≤ (∫ x : ι → ℝ, frobSq (∑ i, x i • A i) ∂gaussianVector ι)/(L^2) :=
      (le_div_iff₀ (sq_pos_of_pos hL)).mpr (by simpa only [mul_comm] using hm)
    _ ≤ ((Fintype.card d : ℝ)^2*bilinearSquareMass A Finset.univ)/(L^2) :=
      div_le_div_of_nonneg_right (integral_frobSq_gaussianSeries_le_card_sq_bilinearSquareMass A)
        (sq_nonneg L)
    _ = _ := by rw [hLsq]; field_simp

end NLAlib
