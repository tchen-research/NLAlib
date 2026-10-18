import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventOperatorComparison
import NLAlib.Probability.Gaussian.Comparison.MatrixCoordinateSquareMass
import NLAlib.Probability.Gaussian.Comparison.MatrixResolventEndpoints
import NLAlib.Probability.Transforms.MatrixResolvent
import NLAlib.Probability.Moments.MatrixZeroCovariance
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Matrix-resolvent Gaussian universality

The actual matrix-valued resampling interpolation, the independent-square
Chernoff estimate and the native endpoint laws give a dimension-free
full-covariance comparison with an explicit universal constant.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

private theorem resolvent_comparison_scale_le
    {R v η L T : ℝ} (hR : 0 ≤ R) (hv : 0 ≤ v) (hη : 0 < η)
    (hL : (1 : ℝ) / 2 ≤ L)
    (hmain : T ≤ 72 * (R / η ^ 4 + R ^ 3 / η ^ 6) * (2 * v + R ^ 2 * L))
    (hcrude : T ≤ 2 / η) :
    T ≤ 288 * (R * v + R ^ 3 * L) / η ^ 4 := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  by_cases hlarge : R ≤ η
  · have hratio : 0 ≤ R / η := div_nonneg hR hη.le
    have hratio1 : R / η ≤ 1 := (div_le_one hη).mpr hlarge
    have hratiosq : (R / η) ^ 2 ≤ 1 := by nlinarith
    have hdiv : R ^ 3 / η ^ 6 ≤ R / η ^ 4 := by
      calc
        _ = (R / η ^ 4) * (R / η) ^ 2 := by field_simp
        _ ≤ (R / η ^ 4) * 1 :=
          mul_le_mul_of_nonneg_left hratiosq (by positivity)
        _ = _ := mul_one _
    calc
      T ≤ 72 * (R / η ^ 4 + R ^ 3 / η ^ 6) * (2 * v + R ^ 2 * L) := hmain
      _ ≤ 72 * (2 * (R / η ^ 4)) * (2 * (v + R ^ 2 * L)) := by
        gcongr
        · linarith only [hdiv]
        · nlinarith [mul_nonneg (sq_nonneg R) hL0]
      _ = _ := by field_simp; ring
  · have hηR : η ≤ R := (lt_of_not_ge hlarge).le
    have hcube : η ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hη.le hηR 3
    have hprod : 0 ≤ R ^ 3 * (L - 1 / 2) :=
      mul_nonneg (pow_nonneg hR _) (sub_nonneg.mpr hL)
    have hnum : 2 * η ^ 3 ≤ 288 * (R * v + R ^ 3 * L) := by
      nlinarith [mul_nonneg hR hv, pow_nonneg hR 3]
    calc
      T ≤ 2 / η := hcrude
      _ = (2 * η ^ 3) / η ^ 4 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hnum (pow_nonneg hη.le _)

open MeasureTheory ProbabilityTheory

open scoped Matrix.Norms.L2Operator in
/-- Matching full real and imaginary Gaussian covariance controls the actual
expected matrix resolvent, with a universal constant `288`. This explicit
coefficient comes from the present estimates; the source leaves it unspecified.
All moments and analytic bounds follow from the stated bounded Hermitian matrix laws. The
family may be empty, and the matrix dimension may be one. For noncentered
increments the same statement uses their raw second-moment sum; centered
increments give exactly the source variance proxy.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Theorem 2.10 and
Section 6.4. The retained `log (2d)` version includes dimension one.
atlas: matrix-resolvent-gaussian-universality -/
theorem specNorm_integral_resolvent_sum_sub_gaussian_le
    {ι n : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype n] [DecidableEq n] [Nonempty n]
    (ν : ι → Measure (Matrix n n ℂ)) [∀ i, IsProbabilityMeasure (ν i)]
    (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
    (ρ : Measure (Matrix n n ℂ))
    (hρ : HasGaussianLaw (matrixRealCoordinates : Matrix n n ℂ →
      ((n × n) ⊕ (n × n)) → ℝ) ρ)
    (hρHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (hmean : (∫ A : Matrix n n ℂ, A ∂ρ) = A₀ +
      ∫ x : ι → Matrix n n ℂ, ∑ i, x i ∂Measure.pi ν)
    (hcov : ∀ a b : (n × n) ⊕ (n × n),
      cov[(fun A : Matrix n n ℂ => matrixRealCoordinates A a),
        (fun A : Matrix n n ℂ => matrixRealCoordinates A b); ρ] =
      cov[(fun x : ι → Matrix n n ℂ => matrixRealCoordinates (∑ i, x i) a),
        (fun x : ι → Matrix n n ℂ => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν])
    (ζ : ℂ) (hζ : 0 < ζ.im) :
    specNorm ((∫ x : ι → Matrix n n ℂ, resolvent (A₀ + ∑ i, x i) ζ ∂Measure.pi ν) -
      ∫ A : Matrix n n ℂ, resolvent A ζ ∂ρ) ≤
      288 * (R * specNorm (∑ i, ∫ A : Matrix n n ℂ, A ^ 2 ∂ν i) +
        R ^ 3 * Real.log (2 * Fintype.card n)) / ζ.im ^ 4 := by
  classical
  have := hρ.isProbabilityMeasure
  let M := Matrix n n ℂ
  let J := (n × n) ⊕ (n × n)
  let E := J → ℝ
  let L : E →L[ℝ] M := hermitianMatrixFromRealCoordinates
  let B : ℝ := Real.log (2 * Fintype.card n)
  have hc : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hc1 : (1 : ℝ) ≤ Fintype.card n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos))
  have hB : (1 : ℝ) / 2 ≤ B := by
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact hlog2.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    let := hi
    have hrho : ρ = Measure.dirac A₀ :=
      eq_dirac_of_matrix_mean_eq_of_zero_coordinate_covariance ρ hρ.memLp_two A₀
        (by simpa using hmean) (fun j => by simpa using hcov j j)
    have hz : (0 : ℝ) ≤ 288 * (R * 0 + R ^ 3 * B) / ζ.im ^ 4 := by positivity
    simpa [hrho, B, specNorm_eq_norm] using hz
  | inr hi =>
    let := hi
    let κ : ι → Measure E := fun i => (ν i).map matrixRealCoordinates
    have (i : ι) : IsProbabilityMeasure (κ i) :=
      (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
    have hν3 (i : ι) : MemLp (id : M → M) 3 (ν i) :=
      MemLp.of_bound aestronglyMeasurable_id R (hBound i)
    have hκ2 (i : ι) : MemLp (id : E → E) 2 (κ i) :=
      memLp_id_map_matrixRealCoordinates (ν i)
        (MemLp.of_bound aestronglyMeasurable_id R (hBound i))
    have hκBound : ∀ i, ∀ᵐ x ∂κ i, specNorm (L x) ≤ R := by
      intro i
      have hm : MeasurableSet {x : E | specNorm (L x) ≤ R} := by
        exact (isClosed_le (by simpa only [specNorm_eq_norm] using L.continuous.norm)
          continuous_const).measurableSet
      apply (ae_map_iff measurable_matrixRealCoordinates.aemeasurable hm).mpr
      filter_upwards [hHerm i, hBound i] with A hA hb
      simpa only [L, hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA] using hb
    let γ := centeredMatrixCoordinateLaw ρ
    have hγ := hasGaussianLaw_id_centeredMatrixCoordinateLaw ρ hρ
    have hγmean := integral_eval_centeredMatrixCoordinateLaw_eq_zero ρ hρ
    have hγcov : ∀ a b : J,
        cov[(fun z : E => z a), (fun z : E => z b); γ] =
        cov[(fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p a),
          (fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p b);
          resamplingTripleMeasure κ] := by
      intro a b
      exact (covariance_eval_centeredMatrixCoordinateLaw ρ hρ a b).trans
        ((hcov a b).trans (covariance_resamplingTripleOriginal_matrixRealCoordinates ν a b).symm)
    have hcomp := specNorm_resamplingInterpolation_sub_le_square_mass κ hκ2 γ hγ
      hγmean hγcov A₀ hA₀ hR hκBound ζ hζ.ne'
    have := hγ.isProbabilityMeasure
    rw [resamplingInterpolation_one_matrix_resolvent_law ν hHerm γ A₀ hA₀ ζ hζ.ne',
      resamplingInterpolation_zero_matrix_resolvent_law ν hν3 ρ hρ hρHerm A₀ hA₀ hmean ζ hζ.ne']
      at hcomp
    have hsq := integrable_and_integral_specNorm_sum_coordinate_sq_le_chernoff ν hR hHerm hBound
    let v := specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i)
    have hv : 0 ≤ v := specNorm_nonneg _
    have hlog : Real.log (Fintype.card n) ≤ B :=
      Real.log_le_log hc (by nlinarith)
    have hEY : (∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2) ∂Measure.pi κ) ≤
        2 * v + R ^ 2 * B := by
      refine hsq.2.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_three]) hv
      · exact mul_le_mul_of_nonneg_left hlog (sq_nonneg R)
    have hmain : specNorm ((∫ x : ι → M, resolvent (A₀ + ∑ i, x i) ζ ∂Measure.pi ν) -
        ∫ A : M, resolvent A ζ ∂ρ) ≤
        72 * (R / ζ.im ^ 4 + R ^ 3 / ζ.im ^ 6) * (2 * v + R ^ 2 * B) := by
      calc
        _ ≤ 72 * (R / ζ.im ^ 4 + R ^ 3 / ζ.im ^ 6) *
            (∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2) ∂Measure.pi κ) := by
          simpa only [abs_of_pos hζ, div_eq_mul_inv, inv_pow] using hcomp
        _ ≤ _ := mul_le_mul_of_nonneg_left hEY (by positivity)
    have hcrude := specNorm_integral_resolvent_sub_integral_resolvent_le
      (Measure.pi ν) ρ (fun x : ι → M => A₀ + ∑ i, x i) id (by fun_prop) (by fun_prop)
      ((ae_isHermitian_sum_pi ν hHerm).mono fun x hx => hA₀.add hx) hρHerm ζ hζ.ne'
    have hcrude' : specNorm ((∫ x : ι → M, resolvent (A₀ + ∑ i, x i) ζ ∂Measure.pi ν) -
        ∫ A : M, resolvent A ζ ∂ρ) ≤ 2 / ζ.im := by
      simpa only [id_eq, abs_of_pos hζ, div_eq_mul_inv] using hcrude
    exact resolvent_comparison_scale_le hR hv hζ hB hmain hcrude'


end NLAlib
