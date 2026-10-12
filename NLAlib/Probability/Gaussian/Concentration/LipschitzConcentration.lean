import NLAlib.Probability.Gaussian.Concentration.LogSobolevHerbst

/-!
# Gaussian concentration of Lipschitz functions

For `f : (ι → ℝ) → ℝ` that is `L`-Lipschitz for the Euclidean distance,
`|f x - f y| ≤ L √(∑ᵢ (xᵢ - yᵢ)²)`, and the standard Gaussian measure `γₙ = ⊗ᵢ N(0,1)`:

* `gaussian_concentration_pi`: `f ∈ L¹(γₙ)` and `γₙ{f ≥ 𝔼 f + L t} ≤ e^{-t²/2}`;
The Gaussian-matrix form `gaussian_concentration` is in
`NLAlib.RandomMatrix.Gaussian.Basic.LipschitzConcentration`.

Proof: `γₙ` satisfies the Euclidean log-Sobolev inequality with constant `1`
(`hasEuclideanLogSobolev_pi_gaussianReal`), and the general Herbst argument
(`integrable_of_logSobolev_of_lipschitz`, `measure_ge_le_of_logSobolev`, in
`NLAlib.Probability.Gaussian.Concentration.LogSobolevHerbst`) gives integrability and the tail
`exp(-(L t)²/(2 L²))`. The deterministic smoothing of Lipschitz functions is in
`NLAlib.ForMathlib.Analysis.LipschitzApprox`.

Source: HMT 2011, Prop 10.3; Vershynin 2012, Prop 5.34; Ledoux, *The Concentration of Measure
Phenomenon*, (5.5)–Thm 5.3; Boucheron–Lugosi–Massart 2013, Thm 5.6.
Atlas: `gaussian-concentration`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Concentration -/

/-- **Gaussian concentration** for Lipschitz functions of a standard Gaussian vector: for `f`
`L`-Lipschitz (Euclidean, `L > 0`) on `ι → ℝ` and `t ≥ 0`, `f` is `γₙ`-integrable and
`γₙ{x | 𝔼 f + L t ≤ f x} ≤ e^{-t²/2}`.
Source: Ledoux, *The Concentration of Measure Phenomenon*, Thm 5.3 / (2.35);
Boucheron–Lugosi–Massart 2013, Thm 5.6; Vershynin 2012, Prop 5.34. Atlas:
`gaussian-concentration`. Ported from Prove2me solution
`GaussianMatrix.gaussian_concentration_vector`.
atlas: gaussian-concentration -/
theorem gaussian_concentration_pi {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hL : 0 < L) (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    (Measure.pi fun _ : ι => gaussianReal 0 1)
        {x | (∫ y, f y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + L * t ≤ f x}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  classical
  refine ⟨integrable_of_logSobolev_of_lipschitz hasEuclideanLogSobolev_pi_gaussianReal f L hL.le
    hLip, ?_⟩
  refine (measure_ge_le_of_logSobolev hasEuclideanLogSobolev_pi_gaussianReal f L hL.le hLip
    (L * t) (mul_nonneg hL.le ht)).trans (le_of_eq ?_)
  have hL0 := hL.ne'
  congr 2
  field_simp

end NLAlib
