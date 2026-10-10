import NLAlib.Gaussian.InverseMoments.Probe
import NLAlib.Gaussian.InverseMoments.GammaBounds
import NLAlib.ForMathlib.MeasureTheory.MomentInterpolation

/-!
# Sharp inverse spectral moments from quadratic probes

The Gaussian quadratic-probe comparison proves all positive real inverse
spectral moments up to half the oversampling gap. It retains the sharp
arithmetic-progression constant k+r-1 and gives the expected pseudoinverse norm
directly. No smallest-eigenvalue density theorem is used.

Atlas: inverse-wishart-spectral-moment and pinv-spectral-expectation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The endpoint inverse spectral moment has the sharp arithmetic-progression
constant. Source: operator rederivations, quadratic-probe and Gamma estimates;
atlas inverse-wishart-spectral-moment.
atlas: inverse-wishart-spectral-moment-real-sharp -/
theorem integrable_and_integral_half_gap_rpow_specNorm_inv_gaussianMatrix_le
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r < k) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ (((k : ℝ) - r) / 2))
      (gaussianMatrix r k) ∧
    (∫ G : Fin r → Fin k → ℝ,
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ (((k : ℝ) - r) / 2)
      ∂(gaussianMatrix r k)) ≤
      (Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) / (2 * ((k : ℝ) - r) ^ 2)) ^
        (((k : ℝ) - r) / 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hgap : (0 : ℝ) < (k : ℝ) - r := sub_pos.mpr (by exact_mod_cast hrk)
  let q : ℝ := ((k : ℝ) - r) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨hint, hbound⟩ :=
    integrable_and_integral_rpow_specNorm_inv_self_mul_transpose_gaussianMatrix_le
      hr hrk.le q hq (by dsimp [q]; linarith)
  refine ⟨hint, hbound.trans ?_⟩
  have h1 : (r : ℝ) / 2 + q = (k : ℝ) / 2 := by dsimp [q]; ring
  have h2 : ((k : ℝ) - r + 1) / 2 - q = 1 / 2 := by dsimp [q]; ring
  have h3 : q + 1 / 2 = ((k : ℝ) - r + 1) / 2 := by dsimp [q]; ring
  rw [h1, h2, h3, Real.Gamma_one_half_eq]
  have hnorm :
      Real.Gamma ((k : ℝ) / 2) * Real.sqrt Real.pi * Real.sqrt Real.pi /
        (2 ^ q * Real.Gamma ((r : ℝ) / 2) *
          Real.Gamma (((k : ℝ) - r + 1) / 2) *
          Real.Gamma (((k : ℝ) - r + 1) / 2)) =
      2 ^ (-q) * Real.pi * Real.Gamma ((k : ℝ) / 2) /
        (Real.Gamma ((r : ℝ) / 2) *
          Real.Gamma (((k : ℝ) - r + 1) / 2) ^ 2) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hG1 := (Real.Gamma_pos_of_pos (show 0 < (r : ℝ) / 2 by positivity)).ne'
    have hG2 := (Real.Gamma_pos_of_pos
      (show 0 < ((k : ℝ) - r + 1) / 2 by linarith)).ne'
    have hpow := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) q).ne'
    field_simp
    rw [Real.sq_sqrt Real.pi_pos.le]
  rw [hnorm]
  simpa only [q, neg_div] using gamma_inverse_spectral_endpoint_le hr hrk

/-- Every positive real inverse spectral moment up to half the oversampling gap
is integrable and bounded by the sharp k+r-1 constant. Source: quadratic-probe
operator proof and positive moment comparison; atlas inverse-wishart-spectral-moment.
This allows powers below one and removes the source restriction p ≤ 18.
atlas: inverse-wishart-spectral-moment-real-sharp -/
theorem integrable_and_integral_rpow_specNorm_inv_gaussianMatrix_le_sharp
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r < k) {p : ℝ} (hp : 0 < p)
    (hpq : p ≤ ((k : ℝ) - r) / 2) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p) (gaussianMatrix r k) ∧
    (∫ G : Fin r → Fin k → ℝ,
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p ∂(gaussianMatrix r k)) ≤
      (Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) / (2 * ((k : ℝ) - r) ^ 2)) ^ p := by
  obtain ⟨hint, hbound⟩ :=
    integrable_and_integral_half_gap_rpow_specNorm_inv_gaussianMatrix_le hr hrk
  have hC : 0 ≤ Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) /
      (2 * ((k : ℝ) - r) ^ 2) := by
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hkR : (r : ℝ) < k := by exact_mod_cast hrk
    apply div_nonneg
    · exact mul_nonneg (sq_nonneg _) (by linarith)
    · positivity
  exact integrable_and_integral_rpow_le_of_integral_rpow_le
    measurable_specNorm_inv_self_mul_transpose.aestronglyMeasurable
    (fun _ => specNorm_nonneg _) hp hpq hC hint hbound

/-- The rooted inverse spectral moment bound for arbitrary positive real powers.
Source: quadratic-probe operator proof; atlas inverse-wishart-spectral-moment.
The rooted quantity is not described as a norm when p is below one.
atlas: inverse-wishart-spectral-moment-real-sharp -/
theorem integral_rpow_specNorm_inv_gaussianMatrix_rpow_inv_le_sharp
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r < k) {p : ℝ} (hp : 0 < p)
    (hpq : p ≤ ((k : ℝ) - r) / 2) :
    (∫ G : Fin r → Fin k → ℝ,
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p ∂(gaussianMatrix r k)) ^ p⁻¹ ≤
      Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) / (2 * ((k : ℝ) - r) ^ 2) := by
  obtain ⟨hint, hbound⟩ :=
    integrable_and_integral_rpow_specNorm_inv_gaussianMatrix_le_sharp hr hrk hp hpq
  have hnonneg : 0 ≤ ∫ G : Fin r → Fin k → ℝ,
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p ∂(gaussianMatrix r k) :=
    integral_nonneg fun _ => Real.rpow_nonneg (specNorm_nonneg _) _
  have hC : 0 ≤ Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) /
      (2 * ((k : ℝ) - r) ^ 2) := by
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hkR : (r : ℝ) < k := by exact_mod_cast hrk
    apply div_nonneg
    · exact mul_nonneg (sq_nonneg _) (by linarith)
    · positivity
  calc _ ≤
      ((Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) /
        (2 * ((k : ℝ) - r) ^ 2)) ^ p) ^ p⁻¹ :=
      Real.rpow_le_rpow hnonneg hbound (by positivity)
    _ = _ := Real.rpow_rpow_inv hC hp.ne'

/-- The expected pseudoinverse spectral norm has the sharpened k+r-1 constant.
Source: operator rederivations and the half-power inverse spectral moment;
atlas pinv-spectral-expectation. This also includes the one-row case.
atlas: pinv-spectral-expectation-sharp -/
theorem integrable_and_integral_specNorm_pinvR_gaussianMatrix_le_sharp
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r < k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G)))
      (gaussianMatrix r k) ∧
    (∫ G : Fin r → Fin k → ℝ, specNorm (pinvR (Matrix.of G)) ∂(gaussianMatrix r k)) ≤
      Real.exp 1 / ((k : ℝ) - r) * Real.sqrt (((k : ℝ) + r - 1) / 2) := by
  have hgap : (0 : ℝ) < (k : ℝ) - r := sub_pos.mpr (by exact_mod_cast hrk)
  have hgap1 : (1 : ℝ) ≤ (k : ℝ) - r := by
    have h : ((r + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
    push_cast at h
    linarith
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hkR : (r : ℝ) < k := by exact_mod_cast hrk
  have hnum : 0 ≤ ((k : ℝ) + r - 1) / 2 := by linarith
  obtain ⟨hint, hbound⟩ :=
    integrable_and_integral_rpow_specNorm_inv_gaussianMatrix_le_sharp
      hr hrk (p := 1 / 2) (by norm_num) (by linarith)
  have hf : (fun G : Fin r → Fin k → ℝ =>
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ (1 / 2 : ℝ)) =
      (fun G => specNorm (pinvR (Matrix.of G))) := by
    funext G
    rw [← specNorm_pinvR_sq, ← Real.rpow_natCast, ← Real.rpow_mul (specNorm_nonneg _)]
    norm_num
  rw [hf] at hint hbound
  refine ⟨hint, hbound.trans_eq ?_⟩
  let B : ℝ := Real.exp 1 / ((k : ℝ) - r) * Real.sqrt (((k : ℝ) + r - 1) / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCsq : Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) /
      (2 * ((k : ℝ) - r) ^ 2) = B ^ 2 := by
    dsimp [B]
    rw [mul_pow, div_pow, Real.sq_sqrt hnum]
    field_simp [hgap.ne']
  change (Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) /
    (2 * ((k : ℝ) - r) ^ 2)) ^ (1 / 2 : ℝ) = B
  rw [hCsq, ← Real.rpow_natCast, ← Real.rpow_mul hB]
  norm_num

end NLAlib
