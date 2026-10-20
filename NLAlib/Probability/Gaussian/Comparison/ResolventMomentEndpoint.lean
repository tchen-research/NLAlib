import NLAlib.Probability.Gaussian.Comparison.ResolventMomentDerivativeEstimate
import NLAlib.ForMathlib.Analysis.RpowComparison

/-!
# Actual rooted resolvent-moment interpolation endpoints

The derivative estimate is applied to the genuine real Gram-moment path.
Continuity and strict positivity are proved from its actual law. Empty matrix
dimensions use the native zero trace instead. No root differentiability or
power-weighted derivative inequality is assumed.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 6.9.
Prerequisite for independent-sum-spectrum-universality.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- The roots of the actual two interpolation endpoint Gram moments differ
by at most the explicit square-mass bound. All analytic premises are derived
from the actual laws. The zero-radius and empty-matrix cases are included. -/
theorem abs_resamplingInterpolation_resolventEvenMoment_rpow_inv_sub_le
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun q : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal q i),
          (fun q : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal q j);
          resamplingTripleMeasure ν])
    {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ x ∂ν i, specNorm (L x) ≤ R)
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) (hsmall : 16 * (p : ℝ) * R ≤ |ζ.im|) :
    let F := resamplingInterpolation ν γ (fun x => resolventEvenMoment (A + L x) ζ p)
    let B := lpNorm (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2))
      (2 * (p : ℝ≥0∞)) (Measure.pi ν)
    |F 1 ^ (1 / ((2 * p : ℕ) : ℝ)) - F 0 ^ (1 / ((2 * p : ℕ) : ℝ))| ≤
      9 * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) * R * B * (|ζ.im|⁻¹) ^ 4 := by
  let := hγ.isProbabilityMeasure
  dsimp only
  let F := resamplingInterpolation ν γ (fun x => resolventEvenMoment (A + L x) ζ p)
  let B := lpNorm (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2))
    (2 * (p : ℝ≥0∞)) (Measure.pi ν)
  change |F 1 ^ (1 / ((2 * p : ℕ) : ℝ)) - F 0 ^ (1 / ((2 * p : ℕ) : ℝ))| ≤
    9 * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) * R * B * (|ζ.im|⁻¹) ^ 4
  have hB : 0 ≤ B := lpNorm_nonneg
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hFzero (t : ℝ) : F t = 0 := by
      dsimp only [F, resamplingInterpolation]
      simp [resolventEvenMoment, normalizedTrace]
    rw [hFzero, hFzero, sub_self, abs_zero]
    positivity
  | inr hn =>
    let s : ℝ := 1 / ((2 * p : ℕ) : ℝ)
    let α : ℝ := ((2 * p - 1 : ℕ) : ℝ) / ((2 * p : ℕ) : ℝ)
    let K : ℝ := 9 * ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) *
      ((2 * p + 2 : ℕ) : ℝ) * R * B * (|ζ.im|⁻¹) ^ 4
    have hk : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by positivity
    have hs : 0 ≤ s := by dsimp only [s]; positivity
    have hα : α = 1 - s := by
      have hnum : ((2 * p - 1 : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * p)]
        norm_num
      dsimp only [α, s]
      rw [hnum]
      field_simp
    have hFc : Continuous F :=
      continuous_resamplingInterpolation_resolventEvenMoment ν hν γ A hA hζ hp
    have hFpos (x : ℝ) : 0 < F x :=
      resamplingInterpolation_resolventEvenMoment_pos ν γ A hA hζ hp x
    have hD (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :=
      hasDerivAt_resamplingInterpolation_resolventEvenMoment_and_abs_deriv_le
        ν hν γ hγ hmean hcov hR hBound A hA ζ hζ hp hsmall hx.1 hx.2
    have hDbound (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
        |deriv F x| ≤ K * F x ^ (1 - s) := by
      have hb := (hD x hx).2
      change |deriv F x| ≤ 9 * Real.sqrt x * ((2 * p : ℕ) : ℝ) *
        ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) * R * B *
          (|ζ.im|⁻¹) ^ 4 * F x ^ α at hb
      calc
        _ ≤ 9 * Real.sqrt x * ((2 * p : ℕ) : ℝ) *
            ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) * R * B *
              (|ζ.im|⁻¹) ^ 4 * F x ^ α := hb
        _ = Real.sqrt x * (K * F x ^ α) := by dsimp only [K]; ring
        _ ≤ 1 * (K * F x ^ α) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr hx.2.le)
            (mul_nonneg (by dsimp only [K]; positivity) (Real.rpow_nonneg (hFpos x).le α))
        _ = K * F x ^ (1 - s) := by rw [one_mul, hα]
    have he := Real.abs_rpow_sub_rpow_le_of_hasDerivAt_bound
      (f := F) (f' := deriv F) (a := 0) (b := 1) (s := s) (K := K)
      (by norm_num) hs hFc.continuousOn (fun x _ => hFpos x)
      (fun x hx => (hD x hx).1) hDbound
    have hScalar : (s * K) * (1 - 0) =
        9 * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) * R * B * (|ζ.im|⁻¹) ^ 4 := by
      dsimp only [s, K]
      field_simp
      ring
    simpa only [s, hScalar] using he

end NLAlib
