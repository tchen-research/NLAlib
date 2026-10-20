import NLAlib.Probability.Gaussian.Comparison.ResolventMomentEndpoint
import NLAlib.Probability.Gaussian.Comparison.ResolventMomentEndpoints
import NLAlib.Probability.Gaussian.Comparison.MatrixCoordinateSquareMassMoments
import NLAlib.Probability.Moments.MatrixZeroCovariance
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Actual finite high resolvent-moment Gaussian comparison

The native moment interpolation, actual Gaussian endpoints and matrix
Chernoff square-mass moments give a finite high-moment comparison with a
universal numerical constant. The deterministic offset does not enter the
random square mass. Full real and imaginary covariance is preserved.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Theorem 6.8.
This corollary assumes p >= log(d), the regime used in the spectral
comparison. The source theorem holds for every positive integer p;
that unrestricted auxiliary statement is not asserted here.
This is a prerequisite for independent-sum-spectrum-universality, not a
spectral Hausdorff conclusion.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NLAlib

private theorem resolvent_moment_comparison_scale_le
    {p R Q η ℓ T : ℝ} (hp : 1 ≤ p) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hη : 0 < η) (hℓ : ℓ ≤ p)
    (hlarge : 16 * p * R ≤ η →
      T ≤ 9 * (2 * p + 1) * (2 * p + 2) * R *
        ((Real.exp 1 - 1) * Q + R ^ 2 * (ℓ + 2 * p)) * η⁻¹ ^ 4)
    (hcrude : T ≤ η⁻¹) :
    T ≤ 4096 * (p ^ 2 * R * Q + p ^ 3 * R ^ 3) / η ^ 4 := by
  have hp0 : 0 ≤ p := by linarith
  by_cases hlargeη : 16 * p * R ≤ η
  · have hp2 : p ≤ p ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hp) hp0]
    have hC : 9 * (2 * p + 1) * (2 * p + 2) ≤ 108 * p ^ 2 := by nlinarith
    have hB : (Real.exp 1 - 1) * Q + R ^ 2 * (ℓ + 2 * p) ≤ 2 * Q + 3 * p * R ^ 2 := by
      have he : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_three]
      nlinarith [mul_le_mul_of_nonneg_right he hQ,
        mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hℓ)]
    calc
      T ≤ 9 * (2 * p + 1) * (2 * p + 2) * R *
          ((Real.exp 1 - 1) * Q + R ^ 2 * (ℓ + 2 * p)) * η⁻¹ ^ 4 := hlarge hlargeη
      _ ≤ 108 * p ^ 2 * R * (2 * Q + 3 * p * R ^ 2) * η⁻¹ ^ 4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (mul_le_mul_of_nonneg_left hB (by positivity)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hR) (by positivity))
      _ ≤ 4096 * (p ^ 2 * R * Q + p ^ 3 * R ^ 3) * η⁻¹ ^ 4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h₀ : 0 ≤ p ^ 2 * R * Q := by positivity
        have h₁ : 0 ≤ p ^ 3 * R ^ 3 := by positivity
        nlinarith
      _ = _ := by rw [div_eq_mul_inv, inv_pow]
  · have hηR : η ≤ 16 * p * R := (lt_of_not_ge hlargeη).le
    have hηcube := pow_le_pow_left₀ hη.le hηR 3
    have hnum : η ^ 3 ≤ 4096 * (p ^ 2 * R * Q + p ^ 3 * R ^ 3) := by
      have h₀ : 0 ≤ p ^ 2 * R * Q := by positivity
      nlinarith
    calc
      T ≤ η⁻¹ := hcrude
      _ = η ^ 3 / η ^ 4 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hnum (pow_nonneg hη.le _)

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

open scoped Matrix.Norms.L2Operator in
/-- Matching the full real and imaginary entry Gaussian covariance gives an
actual normalized resolvent Gram-moment comparison with universal constant
4096. Every matrix and analytic moment is derived from bounded Hermitian
increment laws. The family and matrix dimensions may be empty and R may be
zero. Noncentered increments use their actual raw second-moment sum; centered
increments give the source variance proxy.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Theorem 6.8,
restricted to p >= log(d). The source theorem holds for every positive
integer p. The restriction suffices for the intended Hausdorff comparison
and is explicit in `hlog`; no unrestricted high-moment theorem is claimed. -/
theorem abs_integral_resolventEvenMoment_rpow_inv_sub_gaussian_le
    {ι n : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype n] [DecidableEq n]
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
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p)
    (hlog : Real.log (Fintype.card n) ≤ (p : ℝ)) :
    |(∫ x : ι → Matrix n n ℂ, resolventEvenMoment (A₀ + ∑ i, x i) ζ p ∂Measure.pi ν) ^
        (1 / ((2 * p : ℕ) : ℝ)) -
      (∫ A : Matrix n n ℂ, resolventEvenMoment A ζ p ∂ρ) ^ (1 / ((2 * p : ℕ) : ℝ))| ≤
      4096 * ((p : ℝ) ^ 2 * R * specNorm (∑ i, ∫ A : Matrix n n ℂ, A ^ 2 ∂ν i) +
        (p : ℝ) ^ 3 * R ^ 3) / |ζ.im| ^ 4 := by
  classical
  have := hρ.isProbabilityMeasure
  have hSecondMomentNonneg : 0 ≤ specNorm (∑ i, ∫ A : Matrix n n ℂ, A ^ 2 ∂ν i) :=
    specNorm_nonneg _
  have hRHS : 0 ≤ 4096 * ((p : ℝ) ^ 2 * R *
      specNorm (∑ i, ∫ A : Matrix n n ℂ, A ^ 2 ∂ν i) + (p : ℝ) ^ 3 * R ^ 3) /
        |ζ.im| ^ 4 := by positivity
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hz (A : Matrix n n ℂ) : resolventEvenMoment A ζ p = 0 := by
      simp [resolventEvenMoment, normalizedTrace]
    simp only [hz, integral_zero, sub_self, abs_zero]
    exact hRHS
  | inr hn =>
    let M := Matrix n n ℂ
    let J := (n × n) ⊕ (n × n)
    let E := J → ℝ
    let L : E →L[ℝ] M := hermitianMatrixFromRealCoordinates
    let Q := specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i)
    have hQ : 0 ≤ Q := specNorm_nonneg _
    cases isEmpty_or_nonempty ι with
    | inl hi =>
      have hρdirac : ρ = Measure.dirac A₀ :=
        eq_dirac_of_matrix_mean_eq_of_zero_coordinate_covariance ρ hρ.memLp_two A₀
          (by simpa using hmean) (fun j => by simpa using hcov j j)
      have hzero :
          (∫ x : ι → M, resolventEvenMoment (A₀ + ∑ i, x i) ζ p ∂Measure.pi ν) ^
              (1 / ((2 * p : ℕ) : ℝ)) -
            (∫ A : M, resolventEvenMoment A ζ p ∂ρ) ^ (1 / ((2 * p : ℕ) : ℝ)) = 0 := by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, hρdirac]
        rw [integral_const, probReal_univ, one_smul, integral_dirac]
        exact sub_self _
      rw [hzero, abs_zero]
      exact hRHS
    | inr hi =>
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
        have hm : MeasurableSet {x : E | specNorm (L x) ≤ R} :=
          (isClosed_le (by simpa only [specNorm_eq_norm] using L.continuous.norm)
            continuous_const).measurableSet
        apply (ae_map_iff measurable_matrixRealCoordinates.aemeasurable hm).mpr
        filter_upwards [hHerm i, hBound i] with A hA hb
        change specNorm (hermitianMatrixFromRealCoordinates (matrixRealCoordinates A)) ≤ R
        rw [hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA]
        exact hb
      let γ := centeredMatrixCoordinateLaw ρ
      have hγ := hasGaussianLaw_id_centeredMatrixCoordinateLaw ρ hρ
      have hγmean := integral_eval_centeredMatrixCoordinateLaw_eq_zero ρ hρ
      have := hγ.isProbabilityMeasure
      have hγcov : ∀ a b : J,
          cov[(fun z : E => z a), (fun z : E => z b); γ] =
          cov[(fun q : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal q a),
            (fun q : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal q b);
            resamplingTripleMeasure κ] := by
        intro a b
        exact (covariance_eval_centeredMatrixCoordinateLaw ρ hρ a b).trans
          ((hcov a b).trans (covariance_resamplingTripleOriginal_matrixRealCoordinates ν a b).symm)
      have hMoment := memLp_and_lpNorm_specNorm_sum_coordinate_sq_le_chernoff
        ν hR hHerm hBound (Nat.mul_pos (by decide : 0 < 2) hp)
      have hMomentBound : lpNorm (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2))
          (2 * (p : ℝ≥0∞)) (Measure.pi κ) ≤
          (Real.exp 1 - 1) * Q + R ^ 2 * (Real.log (Fintype.card n) + 2 * (p : ℝ)) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hMoment.2
      have hLarge (hη : 16 * (p : ℝ) * R ≤ |ζ.im|) :
          |(∫ x : ι → M, resolventEvenMoment (A₀ + ∑ i, x i) ζ p ∂Measure.pi ν) ^
              (1 / ((2 * p : ℕ) : ℝ)) -
            (∫ A : M, resolventEvenMoment A ζ p ∂ρ) ^ (1 / ((2 * p : ℕ) : ℝ))| ≤
          9 * (2 * (p : ℝ) + 1) * (2 * (p : ℝ) + 2) * R *
            ((Real.exp 1 - 1) * Q + R ^ 2 * (Real.log (Fintype.card n) + 2 * (p : ℝ))) *
              |ζ.im|⁻¹ ^ 4 := by
        have he := abs_resamplingInterpolation_resolventEvenMoment_rpow_inv_sub_le
          κ hκ2 γ hγ hγmean hγcov hR hκBound A₀ hA₀ ζ hζ hp hη
        dsimp only at he
        rw [resamplingInterpolation_one_matrix_resolventEvenMoment_law ν hHerm γ A₀ hA₀ ζ hζ p,
          resamplingInterpolation_zero_matrix_resolventEvenMoment_law ν hν3 ρ hρ hρHerm A₀ hA₀ hmean ζ hζ p]
          at he
        have hCoeff : 0 ≤ 9 * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) * R := by positivity
        have hb := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMomentBound hCoeff) (by positivity : 0 ≤ |ζ.im|⁻¹ ^ 4)
        exact he.trans (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb)
      have hCrude := abs_integral_resolventEvenMoment_rpow_inv_sub_le
        (Measure.pi ν) ρ (fun x : ι → M => A₀ + ∑ i, x i) id
        (by fun_prop) (by fun_prop)
        ((ae_isHermitian_sum_pi ν hHerm).mono fun x hx => hA₀.add hx) hρHerm hζ hp
      exact resolvent_moment_comparison_scale_le
        (by exact_mod_cast (Nat.succ_le_iff.mpr hp)) hR hQ (abs_pos.mpr hζ) hlog hLarge hCrude

end NLAlib
