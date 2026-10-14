import NLAlib.Probability.Gaussian.Moments.NaturalMoments
import NLAlib.Probability.Moments.Euclidean
import Mathlib.MeasureTheory.Integral.Prod

/-! # Gaussian averaging of directional moments

Integrating an independent Gaussian probe in both orders retains the scalar
Gaussian factorial saving in a Euclidean radial moment bound.
Source: Heidary, *The Sharp Logarithmic Cost of Khatri--Rao Subspace
Embeddings*, equation `variance:eq:row-moment`.
Atlas: `khatri-rao-sharp-growth`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Finset

namespace NLAlib

/-- Gaussian averaging converts a homogeneous directional even-moment budget
into a radial budget, retaining its exact scalar Gaussian divisor.
Source: Heidary, equation `variance:eq:row-moment`.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_gaussianEvenMoment_mul_integral_dotProduct_self_pow_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {r p : ℕ} (hr : 1 ≤ r) (hp : 1 ≤ p) (y : Ω → Fin r → ℝ)
    (hy : Measurable y) {A : ℝ} (hA : 0 ≤ A)
    (hdir : ∀ a : Fin r → ℝ,
      Integrable (fun ω => (a ⬝ᵥ y ω) ^ (2 * p)) μ ∧
        (∫ ω, (a ⬝ᵥ y ω) ^ (2 * p) ∂μ) ≤ A * (a ⬝ᵥ a) ^ p) :
    Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ ∧
      gaussianEvenMoment p * (∫ ω, (y ω ⬝ᵥ y ω) ^ p ∂μ) ≤
        A * gaussianRadialMoment r p := by
  have hdirN (a : Fin r → ℝ) :
      Integrable (fun ω => (a ⬝ᵥ y ω) ^ (2 * p)) μ ∧
        (∫ ω, (a ⬝ᵥ y ω) ^ (2 * p) ∂μ) ≤ A * ‖WithLp.toLp 2 a‖ ^ (2 * p) := by
    simpa only [pow_mul, norm_toLp_sq_eq_dotProduct_self] using hdir a
  have hnorm := (integrable_and_integral_norm_mulVec_pow_two_mul_le y hy.aemeasurable
    (by omega) hA hdirN (1 : Matrix (Fin r) (Fin r) ℝ)).1
  simp only [one_mulVec, pow_mul, norm_toLp_sq_eq_dotProduct_self] at hnorm
  let γ := gaussianVector (Fin r)
  have hGN : Integrable (fun g : Fin r → ℝ => (g ⬝ᵥ g) ^ p) γ := by
    simpa only [Real.rpow_natCast, dotProduct, ← pow_two] using
      integrable_rpow_sum_sq_gaussianVector r (p : ℝ) (by positivity)
  have hGI : (∫ g : Fin r → ℝ, (g ⬝ᵥ g) ^ p ∂γ) = gaussianRadialMoment r p := by
    simpa only [dotProduct, ← pow_two] using integral_pow_sum_sq_gaussianVector hr p
  have hprod : Integrable
      (fun v : (Fin r → ℝ) × Ω => (v.1 ⬝ᵥ y v.2) ^ (2 * p)) (γ.prod μ) := by
    apply (hGN.mul_prod hnorm).mono'
    · apply Measurable.aestronglyMeasurable
      unfold dotProduct
      fun_prop
    · apply Filter.Eventually.of_forall
      intro v
      have hnonneg : 0 ≤ (v.1 ⬝ᵥ y v.2) ^ (2 * p) := by
        rw [pow_mul]
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hcs : (v.1 ⬝ᵥ y v.2) ^ 2 ≤ (v.1 ⬝ᵥ v.1) * (y v.2 ⬝ᵥ y v.2) := by
        simpa only [dotProduct, ← pow_two] using sum_mul_sq_le_sq_mul_sq univ v.1 (y v.2)
      simpa only [pow_mul, mul_pow] using pow_le_pow_left₀ (sq_nonneg _) hcs p
  refine ⟨hnorm, ?_⟩
  calc
    gaussianEvenMoment p * (∫ ω, (y ω ⬝ᵥ y ω) ^ p ∂μ) =
        ∫ ω, ∫ g : Fin r → ℝ, (g ⬝ᵥ y ω) ^ (2 * p) ∂γ ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      simpa only [dotProduct_comm] using
        (integrable_and_integral_dotProduct_pow_two_mul_gaussianVector (y ω) p).2.symm
    _ = ∫ g : Fin r → ℝ, ∫ ω, (g ⬝ᵥ y ω) ^ (2 * p) ∂μ ∂γ :=
      (integral_integral_swap hprod).symm
    _ ≤ ∫ g : Fin r → ℝ, A * (g ⬝ᵥ g) ^ p ∂γ :=
      integral_mono hprod.integral_prod_left (hGN.const_mul A) fun g => (hdir g).2
    _ = A * gaussianRadialMoment r p := by rw [integral_const_mul, hGI]

end NLAlib
