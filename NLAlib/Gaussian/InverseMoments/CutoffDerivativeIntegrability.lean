import NLAlib.Gaussian.InverseMoments.RegularizedIntegrability
import NLAlib.Matrix.GramCutoffCalculus
import NLAlib.Matrix.GramSoftMinMeasurable

/-!
# Integrability of unshifted Gram cutoff derivatives

A positive compact scalar test controls the inverse on its active region.
The actual coordinate derivative of the cutoff Gram gradient therefore has
an explicit Frobenius polynomial majorant under the original Gaussian law.

Source: the user's finite unshifted operator refinement.
Atlas: `wishart-lambda-min-tail` (Stein integrability helper).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Matrix ContDiff

namespace NLAlib

/-- The actual coordinate derivative of a cut off unshifted Gram gradient
is Gaussian integrable. The Hessian is bounded only where the scalar test
is active; no inverse moment or global Hessian-integrability premise is
assumed. Source: positive cutoff bounds and Gaussian polynomial moments;
atlas `wishart-lambda-min-tail` (unshifted Stein helper). -/
theorem integrable_test_unshiftedGramVectorFieldDerivative_single_gaussianMatrix
    {r k : ℕ} (hr : 0 < r) (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi 0) (i : Fin r) (j : Fin k) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      deriv ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
          gramSoftMinGradient n 0 (Matrix.of G) i j ^ 2 +
        ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
          gramSoftMinSecond n 0 (Matrix.of G) (Matrix.single i j 1)) (gaussianMatrix r k) := by
  let : NeZero r := ⟨hr.ne'⟩
  obtain ⟨a, b, ha, hab, hs, _⟩ := exists_pos_bounds_tsupport_and_deriv ψ hψc hψs
  have hb : 0 < b := ha.trans hab
  obtain ⟨P, hP⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨Q, hQ⟩ := (hψ.continuous_deriv (by simp)).bounded_above_of_compact_support hψc.deriv
  have hP0 : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hQ0 : 0 ≤ Q := (norm_nonneg (deriv ψ 0)).trans (hQ 0)
  let M : ℝ := 4 * b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2)
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hD0 : 0 ≤ 4 * Q + P * M := by positivity
  have hFm : Measurable (fun G : Fin r → Fin k → ℝ =>
      inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) := by
    simpa only [regularizedGram_zero] using
      (measurable_inversePowerSoftMin_regularizedGram (ι := Fin r) (κ := Fin k) n 0)
  have hDm := measurable_gramSoftMinGradient_entry (ι := Fin r) (κ := Fin k) n 0 i j
  have hDDm := measurable_gramSoftMinSecond_single (ι := Fin r) (κ := Fin k) n 0 i j
  have hm : Measurable (fun G : Fin r → Fin k → ℝ =>
      deriv ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
          gramSoftMinGradient n 0 (Matrix.of G) i j ^ 2 +
        ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
          gramSoftMinSecond n 0 (Matrix.of G) (Matrix.single i j 1)) :=
    (((hψ.continuous_deriv (by simp)).measurable.comp hFm).mul (hDm.pow_const 2)).add
      ((hψ.continuous.measurable.comp hFm).mul hDDm)
  apply integrable_of_abs_le_frobSq_polynomial_gaussianMatrix r k 1 _ hm (2 * P) (4 * Q + P * M)
  intro G
  let H : Matrix (Fin r) (Fin k) ℝ := Matrix.of G
  let F : ℝ := inversePowerSoftMin n (H * Hᵀ)
  have hG0 : 0 ≤ frobSq H := frobSq_nonneg H
  have hfirst : |deriv ψ F * gramSoftMinGradient n 0 H i j ^ 2| ≤ 4 * Q * frobSq H := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (gramSoftMinGradient n 0 H i j))]
    have htest : |deriv ψ F| ≤ Q := by simpa only [Real.norm_eq_abs] using hQ F
    have hsq := sq_gramSoftMinGradient_unshifted_single_le n hn H i j
    have h := mul_le_mul htest hsq (sq_nonneg _) hQ0
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hsecond : |ψ F * gramSoftMinSecond n 0 H (Matrix.single i j 1)| ≤
      P * (2 + M * frobSq H) := by
    by_cases hzero : ψ F = 0
    · rw [hzero, zero_mul, abs_zero]
      positivity
    · have hmem : F ∈ tsupport ψ := subset_tsupport ψ hzero
      have hbound := abs_gramSoftMinSecond_unshifted_single_le_cutoff n hn H i j a b ha
        (hs hmem).1 (hs hmem).2
      change |gramSoftMinSecond n 0 H (Matrix.single i j 1)| ≤ 2 + M * frobSq H at hbound
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hP F) hbound (abs_nonneg _) hP0
  change |deriv ψ F * gramSoftMinGradient n 0 H i j ^ 2 +
      ψ F * gramSoftMinSecond n 0 H (Matrix.single i j 1)| ≤
      2 * P + (4 * Q + P * M) * (1 + frobSq H) ^ 1
  rw [pow_one]
  calc _ ≤ |deriv ψ F * gramSoftMinGradient n 0 H i j ^ 2| +
        |ψ F * gramSoftMinSecond n 0 H (Matrix.single i j 1)| := abs_add_le _ _
    _ ≤ 4 * Q * frobSq H + P * (2 + M * frobSq H) := add_le_add hfirst hsecond
    _ = 2 * P + (4 * Q + P * M) * frobSq H := by ring
    _ ≤ _ := by
        have hf : frobSq H ≤ 1 + frobSq H := by linarith
        exact add_le_add (le_refl (2 * P)) (mul_le_mul_of_nonneg_left hf hD0)

end NLAlib
