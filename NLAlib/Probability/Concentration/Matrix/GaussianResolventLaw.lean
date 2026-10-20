import NLAlib.Probability.Concentration.Matrix.GaussianResolventSeries
import NLAlib.Probability.Gaussian.Basic.MatrixSeriesRepresentation
import NLAlib.Probability.SubGaussian.Moments
import NLAlib.Matrix.Basic.QuadraticFunctional
import NLAlib.Matrix.Functions.ResolventMeasurability

/-!
# Resolvent-norm concentration for actual Hermitian Gaussian laws

An actual arbitrary centered Hermitian Gaussian law is realized by independent
real standard Gaussian coefficients. Its actual quadratic variance transports
to that realization. The source bilinear sigma-star budget is retained as a
bound on the modulus-squared moments of an arbitrary pair of unit vectors;
its equal-vector restriction suffices for the Gaussian Lipschitz step.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 5.5.
The strict tail includes zero variance, unlike the literal non-strict source
formula at a zero fluctuation threshold. This supports the retained strict-tail
independent-sum-spectrum-universality card.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- The actual centered resolvent spectral norm under an arbitrary centered
Hermitian Gaussian law has the sharp Gaussian MGF budget from unit quadratic
variances. Singular covariance, zero variance and empty matrices are included. -/
theorem hasSubgaussianMGF_specNorm_resolvent_add_gaussian_of_quadratic_variance
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    HasSubgaussianMGF
      (fun Z => specNorm (resolvent (D + Z) ζ) - ∫ H, specNorm (resolvent (D + H) ζ) ∂γ)
      ⟨σ ^ 2 * (|ζ.im|⁻¹) ^ 4, by positivity⟩ γ := by
  obtain ⟨A, hA, hrep⟩ := exists_hermitian_gaussian_series_representation γ hmean hHerm
  let J := (n × n) ⊕ (n × n)
  let S : (J → ℝ) → M := fun x => ∑ i, x i • A i
  have hSm : Measurable S := by fun_prop
  have hid : IdentDistrib S (id : M → M) (gaussianVector J) γ :=
    ⟨hSm.aemeasurable, aemeasurable_id, by simpa only [Measure.map_id] using hrep.symm⟩
  have hvarianceS : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun x : J → ℝ => (quadForm (∑ i, x i • A i) u).re; gaussianVector J] ≤ σ ^ 2 := by
    intro u hu
    have hq : Measurable (fun Z : M => (quadForm Z u).re) := by
      simp only [quadForm, dotProduct, Matrix.mulVec]
      fun_prop
    have he := (hid.comp hq).variance_eq
    have he' : Var[fun x : J → ℝ => (quadForm (∑ i, x i • A i) u).re; gaussianVector J] =
        Var[fun Z => (quadForm Z u).re; γ] := by
      simpa only [Function.comp_def, id_eq, S] using he
    exact he'.trans_le (hvariance u hu)
  have hsg := hasSubgaussianMGF_specNorm_resolvent_affineSeries_of_quadratic_variance
    D hD A hA hσ hvarianceS ζ hζ
  have ho : Measurable (fun Z : M => specNorm (resolvent (D + Z) ζ)) := by
    simpa only [specNorm_eq_norm, Function.comp_def, Pi.add_apply, id_eq] using
      ((measurable_matrix_resolvent ζ).comp (measurable_const.add measurable_id)).norm
  have hobs := hid.comp ho
  simp only [Function.comp_def, id_eq, S] at hobs
  have hmeanobs : (∫ x : J → ℝ, specNorm (resolvent (D + ∑ i, x i • A i) ζ) ∂gaussianVector J) =
      ∫ Z, specNorm (resolvent (D + Z) ζ) ∂γ := hobs.integral_eq
  have hcenter := hobs.sub_const (∫ H, specNorm (resolvent (D + H) ζ) ∂γ)
  have hsg' : HasSubgaussianMGF
      (fun x : J → ℝ => specNorm (resolvent (D + ∑ i, x i • A i) ζ) -
        ∫ H, specNorm (resolvent (D + H) ζ) ∂γ)
      ⟨σ ^ 2 * (|ζ.im|⁻¹) ^ 4, by positivity⟩ (gaussianVector J) := by
    rw [← hmeanobs]
    exact hsg
  exact hsg'.congr_identDistrib hcenter

open scoped Matrix.Norms.L2Operator in
/-- The exact source bilinear sigma-star geometry controls actual Gaussian
resolvent-norm fluctuations. The hypothesis is the modulus-squared second
moment over an arbitrary pair of complex Euclidean unit vectors, and is
not replaced by an entry covariance norm or a normalized trace. No entry
independence, nonsingular covariance or positive sigma premise is imposed. -/
theorem hasSubgaussianMGF_specNorm_resolvent_add_gaussian_of_bilinear_second_moment
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∫ Z, ‖star v ⬝ᵥ (Z *ᵥ w)‖ ^ 2 ∂γ) ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    HasSubgaussianMGF
      (fun Z => specNorm (resolvent (D + Z) ζ) - ∫ H, specNorm (resolvent (D + H) ζ) ∂γ)
      ⟨σ ^ 2 * (|ζ.im|⁻¹) ^ 4, by positivity⟩ γ := by
  apply hasSubgaussianMGF_specNorm_resolvent_add_gaussian_of_quadratic_variance
    γ D hD hHerm hmean hσ _ ζ hζ
  intro u hu
  have hq : Measurable (fun Z : M => (quadForm Z u).re) := by
    exact Complex.measurable_re.comp (quadFormContinuousLinearMap u).continuous.measurable
  have heq : (∫ Z : M, (quadForm Z u).re ^ 2 ∂γ) =
      ∫ Z : M, ‖star u ⬝ᵥ (Z *ᵥ u)‖ ^ 2 ∂γ := by
    apply integral_congr_ae (hHerm.mono fun Z hZ => ?_)
    change (quadForm Z u).re ^ 2 = ‖quadForm Z u‖ ^ 2
    have he := congrArg (fun z : ℂ => ‖z‖ ^ 2) (hZ.ofReal_re_quadForm u)
    change ‖(((quadForm Z u).re : ℝ) : ℂ)‖ ^ 2 = ‖quadForm Z u‖ ^ 2 at he
    rw [Complex.norm_real, Real.norm_eq_abs, _root_.sq_abs] at he
    exact he
  exact (variance_le_expectation_sq hq.aestronglyMeasurable).trans
    (heq.trans_le (hbilinear u u hu hu))

open scoped Matrix.Norms.L2Operator in
/-- The genuine Gaussian resolvent norm has the source two-sided Gaussian
tail with the exact bilinear sigma-star budget. The event is strict, retaining
zero variance, empty dimensions and t=0 without an impossible non-strict
zero-threshold event bound. -/
theorem measureReal_lt_abs_specNorm_resolvent_add_gaussian_sub_mean_le
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hbilinear : ∀ v w : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 → ‖WithLp.toLp 2 w‖ = 1 →
      (∫ Z, ‖star v ⬝ᵥ (Z *ᵥ w)‖ ^ 2 ∂γ) ≤ σ ^ 2)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    γ.real {Z | (σ * (|ζ.im|⁻¹) ^ 2) * t <
      |specNorm (resolvent (D + Z) ζ) - ∫ H, specNorm (resolvent (D + H) ζ) ∂γ|} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  have hsg := hasSubgaussianMGF_specNorm_resolvent_add_gaussian_of_bilinear_second_moment
    γ D hD hHerm hmean hσ hbilinear ζ hζ
  by_cases hσ0 : σ = 0
  · have hzero : (fun Z => specNorm (resolvent (D + Z) ζ) -
        ∫ H, specNorm (resolvent (D + H) ζ) ∂γ) =ᵐ[γ] (0 : M → ℝ) := by
      have hc : (⟨σ ^ 2 * (|ζ.im|⁻¹) ^ 4, by positivity⟩ : NNReal) = 0 := by
        apply NNReal.coe_eq_zero.mp
        change σ ^ 2 * (|ζ.im|⁻¹) ^ 4 = 0
        simp only [hσ0, zero_pow (by decide : 2 ≠ 0), zero_mul]
      rw [hc] at hsg
      exact hsg.ae_eq_zero_of_hasSubgaussianMGF_zero
    have he : {Z : M | (σ * (|ζ.im|⁻¹) ^ 2) * t <
        |specNorm (resolvent (D + Z) ζ) - ∫ H, specNorm (resolvent (D + H) ζ) ∂γ|} =ᵐ[γ]
          (∅ : Set M) := by
      filter_upwards [hzero] with Z hZ
      change specNorm (resolvent (D + Z) ζ) - ∫ H, specNorm (resolvent (D + H) ζ) ∂γ = 0 at hZ
      apply propext
      change ((σ * (|ζ.im|⁻¹) ^ 2) * t <
        |specNorm (resolvent (D + Z) ζ) - ∫ H, specNorm (resolvent (D + H) ζ) ∂γ| ↔ False)
      simp only [hσ0, zero_mul, hZ, abs_zero, lt_self_iff_false]
    rw [measureReal_congr he]
    simp only [measureReal_empty]
    positivity
  · have hη : |ζ.im| ≠ 0 := abs_ne_zero.mpr hζ
    have hb := measureReal_lt_abs_le_of_hasSubgaussianMGF hsg
      (mul_nonneg (by positivity : 0 ≤ σ * (|ζ.im|⁻¹) ^ 2) ht)
    have he : -((σ * (|ζ.im|⁻¹) ^ 2) * t) ^ 2 /
        (2 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4)) = -t ^ 2 / 2 := by
      field_simp [hσ0, hη]
    change γ.real {Z | (σ * (|ζ.im|⁻¹) ^ 2) * t <
      |specNorm (resolvent (D + Z) ζ) - ∫ H, specNorm (resolvent (D + H) ζ) ∂γ|} ≤
        2 * Real.exp (-((σ * (|ζ.im|⁻¹) ^ 2) * t) ^ 2 /
          (2 * (σ ^ 2 * (|ζ.im|⁻¹) ^ 4))) at hb
    rw [he] at hb
    exact hb

end NLAlib
