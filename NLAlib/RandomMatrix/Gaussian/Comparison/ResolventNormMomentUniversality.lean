import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventMomentUniversality
import NLAlib.Probability.Transforms.ResolventNormMoments
import NLAlib.Probability.Concentration.Matrix.GaussianResolventCentering
import NLAlib.ForMathlib.MeasureTheory.LpMarkov

/-!
# Actual scalar resolvent moments under full covariance matching

The previously proved normalized Gram comparison gives the actual scalar
operator-norm Lp comparison, with its exact dimension factor. Markov and
actual Gaussian concentration then give the fixed-parameter upper estimate.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 7.3.
This does not yet assert simultaneous control over a spectral grid.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib

variable {ι n : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)


open scoped Matrix.Norms.L2Operator in
/-- The genuine scalar even Lp resolvent norm is controlled by that of its
full-covariance Gaussian proxy. The exact dimension factor is retained;
there are no entry-independence or positive-variance assumptions. -/
theorem lpNorm_specNorm_resolvent_pi_le_gaussian
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
  (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
  {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
  (ρ : Measure M) [IsGaussian ρ] (hρHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
  (A₀ : M) (hA₀ : A₀.IsHermitian)
  (hmean : (∫ A : M, A ∂ρ) = A₀ + ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
  (hcov : ∀ a b : J,
    cov[(fun A : M => matrixRealCoordinates A a),
      (fun A : M => matrixRealCoordinates A b); ρ] =
    cov[(fun x : ι → M => matrixRealCoordinates (∑ i, x i) a),
      (fun x : ι → M => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν])
  (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p)
  (hlog : Real.log (Fintype.card n) ≤ (p : ℝ)) : lpNorm (fun x : ι → M => specNorm (resolvent (A₀ + ∑ i, x i) ζ))
        (2 * (p : ℝ≥0∞)) (Measure.pi ν) ≤
      (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) *
        (lpNorm (fun A : M => specNorm (resolvent A ζ)) (2 * (p : ℝ≥0∞)) ρ +
          4096 * ((p : ℝ) ^ 2 * R * specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i) +
            (p : ℝ) ^ 3 * R ^ 3) / |ζ.im| ^ 4) := by
  have hρ : HasGaussianLaw (matrixRealCoordinates : M → J → ℝ) ρ := by
    apply ((IsGaussian.hasGaussianLaw_id (μ := ρ)).map_of_measurable
      (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).toContinuousLinearMap
      (by fun_prop)).congr
    exact Filter.Eventually.of_forall fun _ => rfl
  have hc := abs_integral_resolventEvenMoment_rpow_inv_sub_gaussian_le
    ν hHerm hR hBound ρ hρ hρHerm A₀ hA₀ hmean hcov ζ hζ hp hlog
  have hX : ∀ᵐ x : ι → M ∂Measure.pi ν, (A₀ + ∑ i, x i).IsHermitian := by
    have hh : ∀ᵐ x : ι → M ∂Measure.pi ν, ∀ i, (x i).IsHermitian :=
      ae_all_iff.mpr fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hHerm i)
    exact hh.mono fun x hx => hA₀.add (isSelfAdjoint_sum _ fun i _ => hx i)
  have hXm : AEMeasurable (fun x : ι → M => A₀ + ∑ i, x i) (Measure.pi ν) := by fun_prop
  have hupper := lpNorm_specNorm_resolvent_le_card_rpow_mul_integral_resolventEvenMoment_rpow_inv
    (Measure.pi ν) _ hXm hX hζ hp
  have hlower := integral_resolventEvenMoment_rpow_inv_le_lpNorm_specNorm
    ρ id aemeasurable_id hρHerm hζ hp
  simp only [id_eq] at hlower
  apply hupper.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have he := (le_abs_self _).trans hc
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The actual Gaussian resolvent Lp norm is controlled by the original
independent sum with matching full covariance. This is the reverse scalar
moment comparison, including zero variance and empty matrix shapes.
Source: arXiv:2201.05142v3, the moment step of Lemma 7.5.
atlas: independent-sum-spectrum-universality (partial) -/
theorem lpNorm_specNorm_resolvent_gaussian_le_pi
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
  (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
  {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
  (ρ : Measure M) [IsGaussian ρ] (hρHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
  (A₀ : M) (hA₀ : A₀.IsHermitian)
  (hmean : (∫ A : M, A ∂ρ) = A₀ + ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
  (hcov : ∀ a b : J,
    cov[(fun A : M => matrixRealCoordinates A a),
      (fun A : M => matrixRealCoordinates A b); ρ] =
    cov[(fun x : ι → M => matrixRealCoordinates (∑ i, x i) a),
      (fun x : ι → M => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν])
  (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p)
  (hlog : Real.log (Fintype.card n) ≤ (p : ℝ)) : lpNorm (fun A : M => specNorm (resolvent A ζ)) (2 * (p : ℝ≥0∞)) ρ ≤
      (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) *
        (lpNorm (fun x : ι → M => specNorm (resolvent (A₀ + ∑ i, x i) ζ))
        (2 * (p : ℝ≥0∞)) (Measure.pi ν) +
          4096 * ((p : ℝ) ^ 2 * R * specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i) +
            (p : ℝ) ^ 3 * R ^ 3) / |ζ.im| ^ 4) := by
  have hρ : HasGaussianLaw (matrixRealCoordinates : M → J → ℝ) ρ := by
    apply ((IsGaussian.hasGaussianLaw_id (μ := ρ)).map_of_measurable
      (matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).toContinuousLinearMap
      (by fun_prop)).congr
    exact Filter.Eventually.of_forall fun _ => rfl
  have hc := abs_integral_resolventEvenMoment_rpow_inv_sub_gaussian_le
    ν hHerm hR hBound ρ hρ hρHerm A₀ hA₀ hmean hcov ζ hζ hp hlog
  have hX : ∀ᵐ x : ι → M ∂Measure.pi ν, (A₀ + ∑ i, x i).IsHermitian := by
    have hh : ∀ᵐ x : ι → M ∂Measure.pi ν, ∀ i, (x i).IsHermitian :=
      ae_all_iff.mpr fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hHerm i)
    exact hh.mono fun x hx => hA₀.add (isSelfAdjoint_sum _ fun i _ => hx i)
  have hXm : AEMeasurable (fun x : ι → M => A₀ + ∑ i, x i) (Measure.pi ν) := by fun_prop
  have hupper := lpNorm_specNorm_resolvent_le_card_rpow_mul_integral_resolventEvenMoment_rpow_inv
    ρ id aemeasurable_id hρHerm hζ hp
  have hlower := integral_resolventEvenMoment_rpow_inv_le_lpNorm_specNorm
    (Measure.pi ν) _ hXm hX hζ hp
  simp only [id_eq] at hupper
  apply hupper.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have he := (neg_le_abs _).trans hc
  linarith

open scoped Matrix.Norms.L2Operator in
/-- An actual independent sum obeys the fixed-parameter upper resolvent
tail derived from its full-covariance Gaussian proxy. The threshold contains
the actual Gaussian mean, not a supplied high-moment or concentration bound.
Source: arXiv:2201.05142v3, first half of Lemma 7.3.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_specNorm_resolvent_pi_gt_gaussian_mean_le
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
  (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
  {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
  (ρ : Measure M) [IsGaussian ρ] (hρHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
  (A₀ : M) (hA₀ : A₀.IsHermitian)
  (hmean : (∫ A : M, A ∂ρ) = A₀ + ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
  (hcov : ∀ a b : J,
    cov[(fun A : M => matrixRealCoordinates A a),
      (fun A : M => matrixRealCoordinates A b); ρ] =
    cov[(fun x : ι → M => matrixRealCoordinates (∑ i, x i) a),
      (fun x : ι → M => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν])
  (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p)
  (hlog : Real.log (Fintype.card n) ≤ (p : ℝ))
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∫ Z, ‖star v ⬝ᵥ ((Z - ∫ H, H ∂ρ) *ᵥ w)‖ ^ 2 ∂ρ) ≤ σ ^ 2) :
    (Measure.pi ν).real {x : ι → M |
      Real.exp 1 * (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) *
        ((∫ A : M, specNorm (resolvent A ζ) ∂ρ) +
          Real.sqrt (4 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4) * p) +
          4096 * ((p : ℝ) ^ 2 * R * specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i) +
            (p : ℝ) ^ 3 * R ^ 3) / |ζ.im| ^ 4) <
        specNorm (resolvent (A₀ + ∑ i, x i) ζ)} ≤ Real.exp (-((2*p : ℕ) : ℝ)) := by
  have hLp := lpNorm_specNorm_resolvent_pi_le_gaussian
    ν hHerm hR hBound ρ hρHerm A₀ hA₀ hmean hcov ζ hζ hp hlog
  have hG := lpNorm_specNorm_resolvent_gaussian_le_integral_add_sqrt
    ρ hρHerm hσ hbilinear ζ hζ hp
  have hX : ∀ᵐ x : ι → M ∂Measure.pi ν, (A₀ + ∑ i, x i).IsHermitian := by
    have hh : ∀ᵐ x : ι → M ∂Measure.pi ν, ∀ i, (x i).IsHermitian :=
      ae_all_iff.mpr fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hHerm i)
    exact hh.mono fun x hx => hA₀.add (isSelfAdjoint_sum _ fun i _ => hx i)
  have hXm : AEMeasurable (fun x : ι → M => A₀ + ∑ i, x i) (Measure.pi ν) := by fun_prop
  have hmem := memLp_specNorm_resolvent (Measure.pi ν) _ hXm hX hζ (2 * (p : ℝ≥0∞))
  have hmarkov := measureReal_lt_exp_mul_lpNorm_le_exp_neg
    (Nat.mul_pos (by decide : 0 < 2) hp)
    (show MemLp (fun x : ι → M => specNorm (resolvent (A₀ + ∑ i, x i) ζ))
      ((2*p : ℕ) : ℝ≥0∞) (Measure.pi ν) by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmem)
  apply (measureReal_mono (μ := Measure.pi ν) (fun x hx => ?_)).trans hmarkov
  change Real.exp 1 * lpNorm (fun x : ι → M => specNorm (resolvent (A₀ + ∑ i, x i) ζ))
    ((2*p : ℕ) : ℝ≥0∞) (Measure.pi ν) < ‖specNorm (resolvent (A₀ + ∑ i, x i) ζ)‖
  rw [Real.norm_of_nonneg (specNorm_nonneg _)]
  have htotal := hLp.trans (mul_le_mul_of_nonneg_left
    (add_le_add hG le_rfl) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have he := mul_le_mul_of_nonneg_left htotal (Real.exp_pos 1).le
  simp only [Nat.cast_mul, Nat.cast_ofNat] at *
  exact lt_of_le_of_lt (by simpa only [mul_assoc] using he) hx

end NLAlib
