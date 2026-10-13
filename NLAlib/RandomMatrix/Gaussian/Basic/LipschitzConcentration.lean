import NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration
import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix

/-!
# Gaussian concentration for Lipschitz functions of a Gaussian matrix

* `gaussian_concentration`: for `h` on `p × m` matrices, `L`-Lipschitz in the Frobenius norm,
  `P{h(G) ≥ 𝔼 h(G) + L t} ≤ e^{-t²/2}` under `gaussianMatrix (Fin p) (Fin m)` (the vector statement
  `gaussian_concentration_pi` transported through `MeasurableEquiv.curry` and `Matrix.of`).

Moved from `NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration` (dedup round
2026-10-12). Source: HMT 2011, Prop 10.3; Vershynin 2012, Prop 5.34. Atlas:
`gaussian-concentration`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The Frobenius distance of two curried arrays is the Euclidean distance of the flat arrays. -/
private lemma frobNorm_curry_sub {p m : Type*} [Fintype p] [Fintype m] (x y : p × m → ℝ) :
    frobNorm (((MeasurableEquiv.curry p m ℝ).trans Matrix.ofMeasurableEquiv x)
        - ((MeasurableEquiv.curry p m ℝ).trans Matrix.ofMeasurableEquiv y))
      = Real.sqrt (∑ ij, (x ij - y ij) ^ 2) := by
  unfold frobNorm
  rw [frobSq_eq_sum_sq]
  congr 1
  rw [Fintype.sum_prod_type]
  rfl

/-- **Gaussian concentration for Lipschitz functions of a Gaussian matrix**: for
`h` on `p × m` matrices that is `L`-Lipschitz in the Frobenius norm (`L > 0`) and `t ≥ 0`, `h` is
integrable under `gaussianMatrix (Fin p) (Fin m)` and
`P{h(G) ≥ 𝔼 h(G) + L t} ≤ e^{-t²/2}`.
Source: HMT 2011, Prop 10.3; Vershynin 2012, Prop 5.34. Atlas: `gaussian-concentration`.
Ported from Prove2me solution `GaussianMatrix.gaussian_concentration`.
atlas: gaussian-concentration -/
theorem gaussian_concentration {p m : Type*} [Fintype p] [Fintype m] (h : Matrix p m ℝ → ℝ)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (X - Y)) (t : ℝ)
    (ht : 0 ≤ t) :
    Integrable h (gaussianMatrix p m) ∧
    (gaussianMatrix p m).real {X | (∫ Y, h Y ∂(gaussianMatrix p m)) + L * t ≤ h X}
      ≤ Real.exp (-t ^ 2 / 2) := by
  set e := (MeasurableEquiv.curry p m ℝ).trans Matrix.ofMeasurableEquiv with he
  have hg : ∀ x y : p × m → ℝ,
      |(h ∘ e) x - (h ∘ e) y| ≤ L * Real.sqrt (∑ ij, (x ij - y ij) ^ 2) := by
    intro x y
    rw [← frobNorm_curry_sub]
    exact hLip _ _
  obtain ⟨hint, hmeas⟩ := gaussian_concentration_pi (h ∘ e) L hL hg t ht
  rw [gaussianMatrix_eq_map_curry]
  refine ⟨(integrable_map_equiv e h).mpr hint, ?_⟩
  rw [integral_map_equiv, measureReal_def, e.map_apply]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hmeas

/-- `gaussian_concentration` for a random matrix `X` with `HasLaw X (gaussianMatrix p m) μ`:
`P{h(X) ≥ 𝔼 h(G) + L t} ≤ e^{-t²/2}`. Atlas: `gaussian-concentration`. -/
theorem gaussian_concentration_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p m : Type*} [Fintype p] [Fintype m] {X : Ω → Matrix p m ℝ}
    (hX : HasLaw X (gaussianMatrix p m) μ) (h : Matrix p m ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (X - Y)) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | (∫ Y, h Y ∂(gaussianMatrix p m)) + L * t ≤ h (X ω)}
      ≤ Real.exp (-t ^ 2 / 2) := by
  have hc : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro X₀
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have hc : Continuous (fun Y : Matrix p m ℝ => L * frobNorm (Y - X₀)) := by
      unfold frobNorm; simp only [frobSq_eq_sum_sq]; fun_prop
    have h0 : Filter.Tendsto (fun Y : Matrix p m ℝ => L * frobNorm (Y - X₀)) (nhds X₀)
        (nhds 0) := by
      have := hc.tendsto X₀
      simpa [frobNorm, frobSq] using this
    refine squeeze_zero (fun _ => dist_nonneg) (fun Y => ?_) h0
    rw [Real.dist_eq]
    exact hLip Y X₀
  rw [hX.measureReal_eq (p := fun G => (∫ Y, h Y ∂(gaussianMatrix p m)) + L * t ≤ h G)
    (measurableSet_le measurable_const hc.measurable)]
  exact (gaussian_concentration h L hL hLip t ht).2

end NLAlib
