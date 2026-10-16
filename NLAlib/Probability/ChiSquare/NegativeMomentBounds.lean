import NLAlib.Probability.ChiSquare.ChiSquare
import NLAlib.Probability.Moments.Comparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Uniform rooted negative chi-square moments

Positive moment comparison extends the existing endpoint estimate to every
positive exponent at least one half below the integrability threshold.
The small dimensions are handled by the exact Gamma formula.
Source: HMT 2011, Lemma A.10; supplied probability reroutes, W1–W2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

private theorem rooted_inverse_chiSquare_moment_mono {d : ℕ} {q r : ℝ}
    (hq : 0 < q) (hqr : q ≤ r) (hrd : r < (d : ℝ) / 2) :
    (∫ x : Fin d → ℝ, (∑ j, x j ^ 2)⁻¹ ^ q ∂gaussianVector (Fin d)) ^ (1 / q) ≤
      (∫ x : Fin d → ℝ, (∑ j, x j ^ 2)⁻¹ ^ r ∂gaussianVector (Fin d)) ^ (1 / r) := by
  apply (integrable_rpow_and_integral_rpow_inv_le
    (f := fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹) ?_ ?_ hq hqr
    (integrable_rpow_inv_sum_sq_gaussianVector r (hq.trans_le hqr).le hrd)).2
  · exact (by fun_prop : Measurable (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => inv_nonneg.mpr
      (Finset.sum_nonneg fun j _ => sq_nonneg (x j))

/-- Every admissible positive negative moment has rooted size at most `3/d`
in dimension at least five. Source: HMT 2011, Lemma A.10, by endpoint interpolation.
atlas: chi-square-neg-moment (partial) -/
theorem integral_rpow_inv_sum_sq_gaussianVector_root_le_three_div {d : ℕ}
    (hd : 5 ≤ d) {q : ℝ} (hq : 0 < q) (hqd : 2 * q + 1 ≤ (d : ℝ)) :
    (∫ x : Fin d → ℝ, (∑ j, x j ^ 2)⁻¹ ^ q ∂gaussianVector (Fin d)) ^ (1 / q) ≤
      3 / (d : ℝ) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  let r : ℝ := ((d : ℝ) - 1) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hroot := rooted_inverse_chiSquare_moment_mono (d := d) hq (r := r) (by dsimp [r]; linarith)
    (by dsimp [r]; linarith)
  refine hroot.trans ?_
  have hend := (integral_rpow_inv_sum_sq_gaussianVector_lt hd).le
  have hnonneg : 0 ≤ ∫ x : Fin d → ℝ, (∑ j, x j ^ 2)⁻¹ ^ r ∂gaussianVector (Fin d) :=
    integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ ((3 / (d : ℝ)) ^ r) ^ (1 / r) :=
      Real.rpow_le_rpow hnonneg hend (by positivity : 0 ≤ 1 / r)
    _ = _ := by
      rw [← Real.rpow_mul (by positivity : 0 ≤ 3 / (d : ℝ)),
        mul_one_div_cancel hr.ne', Real.rpow_one]

private theorem rooted_inverse_chiSquare_two_le_two :
    (∫ x : Fin 2 → ℝ, (∑ j, x j ^ 2)⁻¹ ^ (1 / 2 : ℝ)
      ∂gaussianVector (Fin 2)) ^ (1 / (1 / 2 : ℝ)) ≤ 2 := by
  rw [integral_rpow_inv_sum_sq_gaussianVector _ (by norm_num) (by norm_num)]
  norm_num [Real.Gamma_one_half_eq, Real.Gamma_one, ← Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt Real.pi_nonneg
  have ht := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.pi_le_four
  have htwo : Real.sqrt 2 ≠ 0 := by positivity
  rw [div_pow]
  exact (div_le_iff₀ (by positivity : 0 < Real.sqrt 2 ^ 2)).mpr (by nlinarith)

private theorem inverse_chiSquare_four_endpoint_le_one :
    (∫ x : Fin 4 → ℝ, (∑ j, x j ^ 2)⁻¹ ^ (3 / 2 : ℝ)
      ∂gaussianVector (Fin 4)) ≤ 1 := by
  rw [integral_rpow_inv_sum_sq_gaussianVector _ (by norm_num) (by norm_num)]
  norm_num [Real.Gamma_one_half_eq, Real.Gamma_two]
  have hs : Real.sqrt Real.pi ≤ 2 := by
    nlinarith [Real.sq_sqrt Real.pi_nonneg, Real.sqrt_nonneg Real.pi, Real.pi_le_four]
  have ht : (2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
  exact (div_le_one (by positivity : (0 : ℝ) < 2 ^ (3 / 2 : ℝ))).mpr (hs.trans ht)

/-- The uniform `4/d` rooted negative-moment bound holds in every admissible
dimension, including dimensions two, three and four. Source: HMT 2011,
Lemma A.10 and supplied reroute W2.
atlas: chi-square-neg-moment (partial) -/
theorem integral_rpow_inv_sum_sq_gaussianVector_root_le_four_div {d : ℕ}
    {q : ℝ} (hq : 0 < q) (hqd : 2 * q + 1 ≤ (d : ℝ)) :
    (∫ x : Fin d → ℝ, (∑ j, x j ^ 2)⁻¹ ^ q ∂gaussianVector (Fin d)) ^ (1 / q) ≤
      4 / (d : ℝ) := by
  by_cases hd : 5 ≤ d
  · exact (integral_rpow_inv_sum_sq_gaussianVector_root_le_three_div hd hq hqd).trans
      (by gcongr; norm_num)
  have hd2 : 2 ≤ d := by
    have : (1 : ℝ) < d := by linarith
    have hd1 : 1 < d := by exact_mod_cast this
    omega
  interval_cases d
  · have h := rooted_inverse_chiSquare_moment_mono (d := 2) hq (r := 1 / 2) (by norm_num at hqd ⊢; linarith)
      (by norm_num)
    have hb := h.trans rooted_inverse_chiSquare_two_le_two
    norm_num at hb ⊢
    exact hb
  · have h := rooted_inverse_chiSquare_moment_mono (d := 3) hq (r := 1) (by norm_num at hqd ⊢; linarith)
      (by norm_num)
    have he : (∫ x : Fin 3 → ℝ, (∑ j, x j ^ 2)⁻¹ ^ (1 : ℝ)
        ∂gaussianVector (Fin 3)) ^ (1 / (1 : ℝ)) = 1 := by
      have hi := integral_inv_sum_sq_gaussianVector (ι := Fin 3) (by norm_num)
      norm_num at hi ⊢
      exact hi
    rw [he] at h
    exact h.trans (by norm_num)
  · have h := rooted_inverse_chiSquare_moment_mono (d := 4) hq (r := 3 / 2) (by norm_num at hqd ⊢; linarith)
      (by norm_num)
    have hm : 0 ≤ ∫ x : Fin 4 → ℝ, (∑ j, x j ^ 2)⁻¹ ^ (3 / 2 : ℝ)
        ∂gaussianVector (Fin 4) := integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
    have hb := Real.rpow_le_one hm inverse_chiSquare_four_endpoint_le_one
      (by norm_num : 0 ≤ 1 / (3 / 2 : ℝ))
    exact h.trans (by simpa using hb)

/-- Transport the uniform rooted negative-moment bound to a random vector with
the standard Gaussian law on an arbitrary probability space.
Source: HMT 2011, Lemma A.10, and law transport.
atlas: chi-square-neg-moment (partial) -/
theorem integral_rpow_inv_sum_sq_root_le_four_div_of_hasLaw {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ} {X : Ω → Fin d → ℝ}
    (hX : HasLaw X (gaussianVector (Fin d)) μ) {q : ℝ}
    (hq : 0 < q) (hqd : 2 * q + 1 ≤ (d : ℝ)) :
    (∫ ω, (∑ j, X ω j ^ 2)⁻¹ ^ q ∂μ) ^ (1 / q) ≤ 4 / (d : ℝ) := by
  have hf : AEStronglyMeasurable (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹ ^ q)
      (gaussianVector (Fin d)) := (by fun_prop : Measurable _).aestronglyMeasurable
  rw [show (∫ ω, (∑ j, X ω j ^ 2)⁻¹ ^ q ∂μ) =
    ∫ x : Fin d → ℝ, (∑ j, x j ^ 2)⁻¹ ^ q ∂gaussianVector (Fin d) from hX.integral_comp hf]
  exact integral_rpow_inv_sum_sq_gaussianVector_root_le_four_div hq hqd

end NLAlib
