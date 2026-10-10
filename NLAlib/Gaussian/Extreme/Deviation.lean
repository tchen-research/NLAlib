import NLAlib.Gaussian.Extreme.Gordon
import NLAlib.Gaussian.Concentration.LipschitzConcentration

/-!
# Deviation of the extreme singular values of a Gaussian matrix

For an `N × n` standard Gaussian matrix `G` with `n ≥ 1` and `t ≥ 0`,

* `measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix`:
  `P(σ_min(G) ≤ √N − √n − t) ≤ e^{-t²/2}` (atlas `smin-lower-tail`);
* `measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix`:
  `P(‖G‖₂ ≥ √N + √n + t) ≤ e^{-t²/2}`;
* `one_sub_le_measure_sigmaMin_and_specNorm_gaussianMatrix`: with probability at least
  `1 − 2e^{-t²/2}`, `√N − √n − t ≤ σ_min(G)` and `‖G‖₂ ≤ √N + √n + t`
  (atlas `extreme-singular-values-deviation`).

Each tail is Gordon's bound on the expectation (`NLAlib.gordon_extreme_singular_values`) plus
Gaussian concentration for the `1`-Lipschitz functions `σ_min` and `‖·‖₂`
(`NLAlib.gaussian_concentration`, `NLAlib.abs_sigmaMin_sub_sigmaMin_le_frobNorm`,
`NLAlib.abs_specNorm_sub_specNorm_le_frobNorm`). Vershynin 2012, Cor. 5.35;
Davidson–Szarek 2001, Thm II.13.

Proof source: Prove2me workspace, Gaussian Random Matrices series (solutions
`sMin_lower_tail`, `extreme_singular_values_deviation`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- **Lower tail of the smallest singular value.** For an `N × n` standard Gaussian matrix `G`
with `n ≥ 1` and `u ≥ 0`, `P(σ_min(G) ≤ √N − √n − u) ≤ e^{-u²/2}`.

Vershynin 2012, Cor. 5.35 (lower half); Davidson–Szarek 2001, Thm II.13.
Atlas: `smin-lower-tail`. The source's hypothesis `n ≤ N` is not needed and is dropped
(Gordon's lower bound `√N − √n ≤ 𝔼 σ_min` holds for all `N`). Ported from Prove2me solution
`GaussianMatrix.sMin_lower_tail`.
atlas: smin-lower-tail -/
theorem measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix {N n : ℕ} (hn : 1 ≤ n) (u : ℝ)
    (hu : 0 ≤ u) :
    (gaussianMatrix N n) {A | sigmaMin (Matrix.of A) ≤ Real.sqrt N - Real.sqrt n - u}
      ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) := by
  set h : (Fin N → Fin n → ℝ) → ℝ := fun X => -sigmaMin (Matrix.of X) with hh
  have hLip : ∀ X Y, |h X - h Y| ≤ 1 * frobNorm (Matrix.of X - Matrix.of Y) := by
    intro X Y
    have := abs_sigmaMin_sub_sigmaMin_le_frobNorm (Matrix.of X) (Matrix.of Y)
    simp only [hh, one_mul]
    rw [show -sigmaMin (Matrix.of X) - -sigmaMin (Matrix.of Y)
        = -(sigmaMin (Matrix.of X) - sigmaMin (Matrix.of Y)) by ring, abs_neg]
    exact this
  obtain ⟨-, hconc⟩ := gaussian_concentration h 1 one_pos hLip u hu
  obtain ⟨-, -, hmean, -, -⟩ := gordon_extreme_singular_values (N := N) hn
  have hint : ∫ Y, h Y ∂(gaussianMatrix N n)
      = -∫ Y, sigmaMin (Matrix.of Y) ∂(gaussianMatrix N n) := by
    simp only [hh]
    exact integral_neg _
  refine le_trans (measure_mono ?_) hconc
  intro X hX
  simp only [Set.mem_ofPred_eq] at hX ⊢
  rw [hint]
  simp only [hh]
  linarith

/-- **Upper tail of the spectral norm.** For an `N × n` standard Gaussian matrix `G` and
`t ≥ 0`, `P(√N + √n + t ≤ ‖G‖₂) ≤ e^{-t²/2}`.

Vershynin 2012, Cor. 5.35 (upper half); Davidson–Szarek 2001, Thm II.13.
Atlas: `extreme-singular-values-deviation` (one half). The source helper assumes `n ≥ 1`, which
is not needed. Ported from Prove2me solution
`GaussianMatrix.extreme_singular_values_deviation` (`esvd_specNorm_tail`).
atlas: extreme-singular-values-deviation -/
theorem measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix {N n : ℕ} (t : ℝ)
    (ht : 0 ≤ t) :
    (gaussianMatrix N n) {A | Real.sqrt N + Real.sqrt n + t ≤ specNorm (Matrix.of A)}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  set h : (Fin N → Fin n → ℝ) → ℝ := fun X => specNorm (Matrix.of X) with hh
  have hLip : ∀ X Y, |h X - h Y| ≤ 1 * frobNorm (Matrix.of X - Matrix.of Y) := by
    intro X Y
    simp only [hh, one_mul]
    exact abs_specNorm_sub_specNorm_le_frobNorm (Matrix.of X) (Matrix.of Y)
  obtain ⟨-, hconc⟩ := gaussian_concentration h 1 one_pos hLip t ht
  have hmean := integral_specNorm_gaussianMatrix_le_sqrt_add_sqrt (N := N) (n := n)
  refine le_trans (measure_mono ?_) hconc
  intro X hX
  simp only [Set.mem_ofPred_eq, hh] at hX ⊢
  linarith

/-- **Deviation of the extreme singular values.** For an `N × n` standard Gaussian matrix `G`
with `n ≥ 1` and `t ≥ 0`, with probability at least `1 − 2e^{-t²/2}`,
`√N − √n − t ≤ σ_min(G)` and `‖G‖₂ ≤ √N + √n + t`.

Vershynin 2012, Cor. 5.35; Davidson–Szarek 2001, Thm II.13. Union bound over the two tails.
Atlas: `extreme-singular-values-deviation`. Ported from Prove2me solution
`GaussianMatrix.extreme_singular_values_deviation`.
atlas: extreme-singular-values-deviation -/
theorem one_sub_le_measure_sigmaMin_and_specNorm_gaussianMatrix {N n : ℕ} (hn : 1 ≤ n)
    (t : ℝ) (ht : 0 ≤ t) :
    1 - ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2))
      ≤ (gaussianMatrix N n) {A | Real.sqrt N - Real.sqrt n - t ≤ sigmaMin (Matrix.of A) ∧
          specNorm (Matrix.of A) ≤ Real.sqrt N + Real.sqrt n + t} := by
  set μ := gaussianMatrix N n
  set E := {A : Fin N → Fin n → ℝ | Real.sqrt N - Real.sqrt n - t ≤ sigmaMin (Matrix.of A) ∧
          specNorm (Matrix.of A) ≤ Real.sqrt N + Real.sqrt n + t} with hE
  set S1 := {A : Fin N → Fin n → ℝ | sigmaMin (Matrix.of A) ≤ Real.sqrt N - Real.sqrt n - t}
  set S2 := {A : Fin N → Fin n → ℝ | Real.sqrt N + Real.sqrt n + t ≤ specNorm (Matrix.of A)}
  have hsub : Eᶜ ⊆ S1 ∪ S2 := by
    intro X hX
    simp only [hE, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hX
    rcases hX with hX | hX
    · exact Or.inl (le_of_lt hX)
    · exact Or.inr (le_of_lt hX)
  have hc : μ Eᶜ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
    have hpos : 0 ≤ Real.exp (-t ^ 2 / 2) := (Real.exp_pos _).le
    rw [two_mul, ENNReal.ofReal_add hpos hpos]
    calc μ Eᶜ ≤ μ (S1 ∪ S2) := measure_mono hsub
      _ ≤ μ S1 + μ S2 := measure_union_le _ _
      _ ≤ _ := add_le_add (measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix hn t ht)
          (measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix t ht)
  have h1 : (1 : ENNReal) ≤ μ E + μ Eᶜ := by
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ = μ (E ∪ Eᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ E + μ Eᶜ := measure_union_le _ _
  rw [tsub_le_iff_right]
  exact h1.trans (add_le_add le_rfl hc)

end NLAlib
