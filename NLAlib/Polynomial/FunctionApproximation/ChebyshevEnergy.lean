import NLAlib.Polynomial.FunctionApproximation.ChebyshevCoefficients
import NLAlib.ForMathlib.Analysis.Calculus.LipschitzComposition
import NLAlib.ForMathlib.Analysis.SineBessel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sharp Chebyshev coefficient energy for Lipschitz functions

The absolutely continuous cosine pullback has derivative bounded by `L sin θ`.
Integration by parts and finite sine Bessel give the sharp univariate energy
bound. No differentiability of the outer Lipschitz function or termwise
differentiation of an infinite Chebyshev expansion is assumed.

Source: Musco--Musco--Rosenblatt--Singh, arXiv:2408.12385v3, Lemma 13;
the measure-analysis roadmap's Lipschitz extension.
Atlas: `chebyshev-lipschitz-coefficient-energy` (univariate part).
-/

noncomputable section

open Real MeasureTheory Set Finset
open scoped Topology

namespace NLAlib

/-- A Lipschitz interval function has an absolutely continuous cosine pullback. -/
theorem absolutelyContinuousOnInterval_comp_cos_of_lipschitzOnWith
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) :
    AbsolutelyContinuousOnInterval (f ∘ cos) 0 π := by
  have hg : LipschitzOnWith L (f ∘ cos) (uIcc (0 : ℝ) π) := by
    simpa only [mul_one] using hf.comp lipschitzWith_cos.lipschitzOnWith
      (fun x _ => ⟨neg_one_le_cos x, cos_le_one x⟩)
  exact hg.absolutelyContinuousOnInterval

/-- The cosine pullback of a Lipschitz function has pointwise speed bounded by
`L |sin θ|`; a nonexistent derivative is zero by Mathlib's convention. -/
theorem abs_deriv_comp_cos_le_of_lipschitzOnWith
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) (θ : ℝ) :
    |deriv (f ∘ cos) θ| ≤ L * |sin θ| := by
  simpa only [Real.norm_eq_abs, Real.deriv_cos, abs_neg] using
    hf.norm_deriv_comp_le differentiableAt_cos
      (Filter.Eventually.of_forall (fun x => ⟨neg_one_le_cos x, cos_le_one x⟩))

/-- The derivative of the cosine pullback has square integral at most `π L²/2`.
Source: the Lipschitz extension of MMRS Lemma 13. -/
theorem integral_sq_deriv_comp_cos_le_of_lipschitzOnWith
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) :
    (∫ θ in (0 : ℝ)..π, deriv (f ∘ cos) θ ^ 2) ≤ π * (L : ℝ) ^ 2 / 2 := by
  have hb (θ : ℝ) : deriv (f ∘ cos) θ ^ 2 ≤ (L : ℝ) ^ 2 * sin θ ^ 2 := by
    have h := abs_deriv_comp_cos_le_of_lipschitzOnWith hf θ
    have hh := mul_self_le_mul_self (abs_nonneg _) h
    simpa only [← sq, mul_pow, sq_abs] using hh
  have hmajor : IntervalIntegrable (fun θ => (L : ℝ) ^ 2 * sin θ ^ 2) volume 0 π :=
    (show Continuous (fun θ => (L : ℝ) ^ 2 * sin θ ^ 2) from by fun_prop).intervalIntegrable _ _
  have hi : IntervalIntegrable (fun θ => deriv (f ∘ cos) θ ^ 2) volume 0 π := by
    apply hmajor.mono_fun' ((measurable_deriv _).pow_const 2).aestronglyMeasurable
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs, abs_sq] using hb θ
  have h := intervalIntegral.integral_mono_on pi_pos.le hi hmajor (fun θ _ => hb θ)
  rw [intervalIntegral.integral_const_mul, integral_sin_sq] at h
  simp only [sin_zero, sin_pi, zero_mul, sub_zero] at h
  convert h using 1
  ring

/-- Integration by parts identifies the positive-frequency Chebyshev coefficient
with the sine coefficient of the negative cosine-pullback derivative.
Source: MMRS Lemma 13, justified for Lipschitz inputs by absolute continuity. -/
theorem integral_neg_deriv_comp_cos_mul_sin_eq
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1))
    {j : ℕ} (hj : 0 < j) :
    (∫ θ in (0 : ℝ)..π, -deriv (f ∘ cos) θ * sin ((j : ℝ) * θ)) =
      π / 2 * ((j : ℝ) * chebyshevCoeff f j) := by
  have hg := absolutelyContinuousOnInterval_comp_cos_of_lipschitzOnWith hf
  have hs : AbsolutelyContinuousOnInterval (fun θ => sin ((j : ℝ) * θ)) 0 π :=
    (show ContDiff ℝ 1 (fun θ => sin ((j : ℝ) * θ)) from by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hd (θ : ℝ) : deriv (fun t => sin ((j : ℝ) * t)) θ =
      (j : ℝ) * cos ((j : ℝ) * θ) := by
    simpa only [id_eq, mul_comm, mul_one] using (((hasDerivAt_id θ).const_mul (j : ℝ)).sin).deriv
  have hi := hg.integral_mul_deriv_eq_deriv_mul hs
  simp only [hd, Function.comp_apply, mul_zero, sin_zero, sin_nat_mul_pi, mul_zero,
    sub_zero, zero_sub] at hi
  have hleft : (∫ θ in (0 : ℝ)..π, f (cos θ) * ((j : ℝ) * cos ((j : ℝ) * θ))) =
      (j : ℝ) * ∫ θ in (0 : ℝ)..π, f (cos θ) * cos ((j : ℝ) * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [hleft] at hi
  simp_rw [neg_mul]
  rw [intervalIntegral.integral_neg, ← hi, chebyshevCoeff_eq_cosine_integral,
    if_neg (by omega : j ≠ 0)]
  field_simp

/-- Any finite set of positive Chebyshev frequencies has weighted energy at most
the squared Lipschitz constant. The constant is sharp already for linear functions.
Source: MMRS Lemma 13, with the standard unnormalized Chebyshev coefficients.
atlas: chebyshev-lipschitz-coefficient-energy (partial) -/
theorem sum_mul_sq_chebyshevCoeff_le_of_lipschitzOnWith
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1))
    (s : Finset ℕ) (hs : ∀ j ∈ s, 0 < j) :
    (∑ j ∈ s, (j : ℝ) ^ 2 * chebyshevCoeff f j ^ 2) ≤ (L : ℝ) ^ 2 := by
  have hg := absolutelyContinuousOnInterval_comp_cos_of_lipschitzOnWith hf
  have hb (θ : ℝ) : deriv (f ∘ cos) θ ^ 2 ≤ (L : ℝ) ^ 2 * sin θ ^ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _)
      (abs_deriv_comp_cos_le_of_lipschitzOnWith hf θ)
    simpa only [← sq, mul_pow, sq_abs] using hh
  have hmajor : IntervalIntegrable (fun θ => (L : ℝ) ^ 2 * sin θ ^ 2) volume 0 π :=
    (show Continuous (fun θ => (L : ℝ) ^ 2 * sin θ ^ 2) from by fun_prop).intervalIntegrable _ _
  have hv2 : IntervalIntegrable (fun θ => (-deriv (f ∘ cos) θ) ^ 2) volume 0 π := by
    apply hmajor.mono_fun' (((measurable_deriv _).neg).pow_const 2).aestronglyMeasurable
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs, Pi.neg_apply, neg_sq, abs_sq] using hb θ
  have h := sum_sq_le_two_div_pi_integral_sq_of_sine_coefficients
    hg.intervalIntegrable_deriv.neg hv2 s hs (fun j => (j : ℝ) * chebyshevCoeff f j)
    (fun j hj => integral_neg_deriv_comp_cos_mul_sin_eq hf (hs j hj))
  simp only [mul_pow, Pi.neg_apply, neg_sq] at h
  refine h.trans ?_
  have henergy := integral_sq_deriv_comp_cos_le_of_lipschitzOnWith hf
  have hm := mul_le_mul_of_nonneg_left henergy (show (0 : ℝ) ≤ 2 / π by positivity)
  convert hm using 1
  field_simp

/-- The positive-frequency weighted Chebyshev energy is summable for every
Lipschitz interval function. Source: finite Bessel bounds, MMRS Lemma 13. -/
theorem summable_mul_sq_chebyshevCoeff_of_lipschitzOnWith
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 2 * chebyshevCoeff f (j + 1) ^ 2) := by
  apply summable_of_sum_le (fun j => by positivity) (c := (L : ℝ) ^ 2)
  intro s
  let e : ℕ ↪ ℕ := ⟨fun j => j + 1, fun _ _ h => Nat.add_right_cancel h⟩
  have h := sum_mul_sq_chebyshevCoeff_le_of_lipschitzOnWith hf (s.map e)
    (fun j hj => by rcases mem_map.mp hj with ⟨k, _, rfl⟩; change 0 < k + 1; omega)
  rw [sum_map] at h
  exact h

/-- The full positive-frequency weighted Chebyshev energy is at most `L²`.
Source: MMRS Lemma 13, extended to Lipschitz functions by an AC pullback.
The tensor assertion on the same atlas card is a separate theorem.
atlas: chebyshev-lipschitz-coefficient-energy (partial) -/
theorem tsum_mul_sq_chebyshevCoeff_le_of_lipschitzOnWith
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) :
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ 2 * chebyshevCoeff f (j + 1) ^ 2) ≤ (L : ℝ) ^ 2 := by
  apply (summable_mul_sq_chebyshevCoeff_of_lipschitzOnWith hf).tsum_le_of_sum_le
  intro s
  let e : ℕ ↪ ℕ := ⟨fun j => j + 1, fun _ _ h => Nat.add_right_cancel h⟩
  have h := sum_mul_sq_chebyshevCoeff_le_of_lipschitzOnWith hf (s.map e)
    (fun j hj => by rcases mem_map.mp hj with ⟨k, _, rfl⟩; change 0 < k + 1; omega)
  rw [sum_map] at h
  exact h

/-- The sharp energy bound is attained by every affine function `c + a x`.
Source: the equality example in MMRS Lemma 13, in standard coefficients.
atlas: chebyshev-lipschitz-coefficient-energy (partial) -/
theorem tsum_mul_sq_chebyshevCoeff_affine (c a : ℝ) :
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ 2 *
      chebyshevCoeff (fun x : ℝ => c + a * x) (j + 1) ^ 2) = a ^ 2 := by
  have hc (k : ℕ) : chebyshevCoeff (fun x : ℝ => c + a * x) k =
      c * (if 0 = k then 1 else 0) + a * (if 1 = k then 1 else 0) := by
    have heq : (fun x : ℝ => c + a * x) = (fun x : ℝ =>
        c * (Polynomial.Chebyshev.T ℝ (0 : ℤ)).eval x +
          a * (Polynomial.Chebyshev.T ℝ (1 : ℤ)).eval x) := by
      funext x
      simp
    rw [heq, chebyshevCoeff_add (by fun_prop) (by fun_prop),
      chebyshevCoeff_const_mul, chebyshevCoeff_const_mul]
    have h0 := chebyshevCoeff_eval_T 0 k
    have h1 := chebyshevCoeff_eval_T 1 k
    norm_num only [Nat.cast_zero, Nat.cast_one] at h0 h1
    rw [h0, h1]
  have heq (j : ℕ) : ((j + 1 : ℕ) : ℝ) ^ 2 *
      chebyshevCoeff (fun x : ℝ => c + a * x) (j + 1) ^ 2 =
        if j = 0 then a ^ 2 else 0 := by
    rw [hc]
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]
  simp_rw [heq]
  simp

end NLAlib
