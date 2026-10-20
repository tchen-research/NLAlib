import NLAlib.Probability.Concentration.Matrix.IndependentResolventTail
import NLAlib.Probability.Concentration.Matrix.ResolventVarianceProxyExpectation

/-!
# Resolvent concentration with a derived deterministic variance bound

Both the random-gradient tail and its actual proxy expectation are proved
from the original independent Hermitian matrix laws. The resulting
deterministic bound keeps the bilinear variance geometry and the native
matrix second-moment sum.

Source: arXiv:2201.05142v3, Proposition 5.6 and Lemmas 5.8--5.9.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    [MeasurableSpace Ω]

/-- Actual independent Hermitian matrix sums have a two-sided resolvent
tail with the computed proxy replaced by its derived expectation bound.
No proxy, gradient, MGF or concentration inequality is a premise.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_gt_abs_centered_specNorm_resolvent_pi_le_of_bilinear_moments
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R v : ℝ} (hR : 0 ≤ R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (hvariance : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖ ^ 2 ∂ν i) ≤ v)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    let B := (2 / |ζ.im| ^ 4) * (8 * v + 64 * R *
      ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν) +
      (32 * R ^ 2 / |ζ.im| ^ 6) * ((Real.exp 1 - 1) *
        specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂ν i) + R ^ 2 * Real.log (Fintype.card n))
    (Measure.pi ν).real {x | Real.sqrt (24 * B * t) +
      Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)) * t <
        |specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) -
          ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν|} ≤
      2 * Real.exp (-t) := by
  let B := (2 / |ζ.im| ^ 4) * (8 * v + 64 * R *
    ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν) +
    (32 * R ^ 2 / |ζ.im| ^ 6) * ((Real.exp 1 - 1) *
      specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂ν i) + R ^ 2 * Real.log (Fintype.card n))
  let E := ∫ q : (ι → Ω) × (ι → Ω),
    resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R |ζ.im|
      ∂((Measure.pi ν).prod (Measure.pi ν))
  have hEB : E ≤ B := (integrable_and_integral_resolventVarianceProxy_copy_pi_le
    ν Z hZm hR (abs_pos.mpr hζ) hZH hZ hmean hvariance).2
  have hs : Real.sqrt (24 * E * t) ≤ Real.sqrt (24 * B * t) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEB (by norm_num)) ht)
  have h := measureReal_gt_abs_centered_specNorm_resolvent_pi_le
    ν A₀ hA₀ Z hZm hR hZH hZ ζ hζ ht
  let c := Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6))
  let f (x : ι → Ω) := |specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) -
    ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν|
  have hset : {x : ι → Ω | Real.sqrt (24 * B * t) + c * t < f x} ⊆
      {x | Real.sqrt (24 * E * t) + c * t < f x} :=
    fun x hx => lt_of_le_of_lt (add_le_add hs (le_refl (c * t))) hx
  exact (measureReal_mono (μ := Measure.pi ν) hset).trans h

end NLAlib
