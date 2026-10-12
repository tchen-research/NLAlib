import NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration
import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix

/-!
# Gaussian concentration for Lipschitz functions of a Gaussian matrix

* `gaussian_concentration`: for `h` on `p × m` arrays, `L`-Lipschitz in the Frobenius norm,
  `P{h(G) ≥ 𝔼 h(G) + L t} ≤ e^{-t²/2}` under `gaussianMatrix p m` (the vector statement
  `gaussian_concentration_pi` transported through `MeasurableEquiv.curry`).

Moved from `NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration` (dedup round
2026-10-12). Source: HMT 2011, Prop 10.3; Vershynin 2012, Prop 5.34. Atlas:
`gaussian-concentration`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The Frobenius distance of two curried arrays is the Euclidean distance of the flat arrays. -/
private lemma frobNorm_curry_sub {p m : ℕ} (x y : Fin p × Fin m → ℝ) :
    frobNorm (Matrix.of (MeasurableEquiv.curry (Fin p) (Fin m) ℝ x)
        - Matrix.of (MeasurableEquiv.curry (Fin p) (Fin m) ℝ y))
      = Real.sqrt (∑ ij, (x ij - y ij) ^ 2) := by
  rw [frobNorm, frobSq_eq_sum_sq]
  congr 1
  rw [Fintype.sum_prod_type]
  rfl

/-- **Gaussian concentration for Lipschitz functions of a Gaussian matrix**: for
`h` on `p × m` arrays that is `L`-Lipschitz in the Frobenius norm (`L > 0`) and `t ≥ 0`, `h` is
integrable under `gaussianMatrix p m` and
`P{h(G) ≥ 𝔼 h(G) + L t} ≤ e^{-t²/2}`.
Source: HMT 2011, Prop 10.3; Vershynin 2012, Prop 5.34. Atlas: `gaussian-concentration`.
Ported from Prove2me solution `GaussianMatrix.gaussian_concentration`.
atlas: gaussian-concentration -/
theorem gaussian_concentration {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) (t : ℝ)
    (ht : 0 ≤ t) :
    Integrable h (gaussianMatrix p m) ∧
    (gaussianMatrix p m) {X | (∫ Y, h Y ∂(gaussianMatrix p m)) + L * t ≤ h X}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  set e := MeasurableEquiv.curry (Fin p) (Fin m) ℝ with he
  have hg : ∀ x y : Fin p × Fin m → ℝ,
      |(h ∘ e) x - (h ∘ e) y| ≤ L * Real.sqrt (∑ ij, (x ij - y ij) ^ 2) := by
    intro x y
    rw [← frobNorm_curry_sub]
    exact hLip _ _
  obtain ⟨hint, hmeas⟩ := gaussian_concentration_pi (h ∘ e) L hL hg t ht
  rw [gaussianMatrix_eq_map_curry]
  refine ⟨(integrable_map_equiv e h).mpr hint, ?_⟩
  rw [integral_map_equiv, e.map_apply]
  exact hmeas

end NLAlib
