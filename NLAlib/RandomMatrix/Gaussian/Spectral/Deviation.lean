import NLAlib.RandomMatrix.Gaussian.Spectral.Gordon
import NLAlib.RandomMatrix.Gaussian.Basic.LipschitzConcentration
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
    (gaussianMatrix (Fin N) (Fin n)).real {A | sigmaMin A ≤ Real.sqrt N - Real.sqrt n - u}
      ≤ Real.exp (-u ^ 2 / 2) := by
  set h : (Matrix (Fin N) (Fin n) ℝ) → ℝ := fun X => -sigmaMin X with hh
  have hLip : ∀ X Y, |h X - h Y| ≤ 1 * frobNorm (X - Y) := by
    intro X Y
    have := abs_sigmaMin_sub_sigmaMin_le_frobNorm X Y
    simp only [hh, one_mul]
    rw [show -sigmaMin X - -sigmaMin Y
        = -(sigmaMin X - sigmaMin Y) by ring, abs_neg]
    exact this
  obtain ⟨-, hconc⟩ := gaussian_concentration h 1 one_pos hLip u hu
  obtain ⟨-, -, hmean, -, -⟩ := gordon_extreme_singular_values (N := N) hn
  have hint : ∫ Y, h Y ∂(gaussianMatrix (Fin N) (Fin n))
      = -∫ Y, sigmaMin Y ∂(gaussianMatrix (Fin N) (Fin n)) := by
    simp only [hh]
    exact integral_neg _
  refine le_trans (measureReal_mono ?_) hconc
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
    (gaussianMatrix (Fin N) (Fin n)).real {A | Real.sqrt N + Real.sqrt n + t ≤ specNorm A}
      ≤ Real.exp (-t ^ 2 / 2) := by
  set h : (Matrix (Fin N) (Fin n) ℝ) → ℝ := fun X => specNorm X with hh
  have hLip : ∀ X Y, |h X - h Y| ≤ 1 * frobNorm (X - Y) := by
    intro X Y
    simp only [hh, one_mul]
    exact abs_specNorm_sub_specNorm_le_frobNorm X Y
  obtain ⟨-, hconc⟩ := gaussian_concentration h 1 one_pos hLip t ht
  have hmean := integral_specNorm_gaussianMatrix_le_sqrt_add_sqrt (N := N) (n := n)
  refine le_trans (measureReal_mono ?_) hconc
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
    1 - 2 * Real.exp (-t ^ 2 / 2)
      ≤ (gaussianMatrix (Fin N) (Fin n)).real {A | Real.sqrt N - Real.sqrt n - t ≤ sigmaMin A ∧
          specNorm A ≤ Real.sqrt N + Real.sqrt n + t} := by
  set μ := gaussianMatrix (Fin N) (Fin n)
  set E := {A : Matrix (Fin N) (Fin n) ℝ | Real.sqrt N - Real.sqrt n - t ≤ sigmaMin A ∧
          specNorm A ≤ Real.sqrt N + Real.sqrt n + t} with hE
  set S1 := {A : Matrix (Fin N) (Fin n) ℝ | sigmaMin A ≤ Real.sqrt N - Real.sqrt n - t}
  set S2 := {A : Matrix (Fin N) (Fin n) ℝ | Real.sqrt N + Real.sqrt n + t ≤ specNorm A}
  have hsub : Eᶜ ⊆ S1 ∪ S2 := by
    intro X hX
    simp only [hE, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hX
    rcases hX with hX | hX
    · exact Or.inl (le_of_lt hX)
    · exact Or.inr (le_of_lt hX)
  have hc : μ.real Eᶜ ≤ 2 * Real.exp (-t ^ 2 / 2) := by
    have h1 := measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix (N := N) hn t ht
    have h2 := measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix (N := N) (n := n) t ht
    calc μ.real Eᶜ ≤ μ.real (S1 ∪ S2) := measureReal_mono hsub
      _ ≤ μ.real S1 + μ.real S2 := measureReal_union_le _ _
      _ ≤ _ := by linarith
  have h1 : (1 : ℝ) ≤ μ.real E + μ.real Eᶜ := by
    calc (1 : ℝ) = μ.real Set.univ := by simp
      _ = μ.real (E ∪ Eᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ.real E + μ.real Eᶜ := measureReal_union_le _ _
  linarith

/-! ### Random matrices with a Gaussian law -/

/-- `measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin N) (Fin n)) μ`. Atlas: `smin-lower-tail`. -/
theorem measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {N n : ℕ} {X : Ω → Matrix (Fin N) (Fin n) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin N) (Fin n)) μ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 ≤ u) :
    μ.real {ω | sigmaMin (X ω) ≤ Real.sqrt N - Real.sqrt n - u} ≤ Real.exp (-u ^ 2 / 2) := by
  have hc : Continuous (sigmaMin : Matrix (Fin N) (Fin n) ℝ → ℝ) :=
    continuous_of_abs_sub_le_mul_frobNorm sigmaMin 1 fun X Y => by
      rw [one_mul]; exact abs_sigmaMin_sub_sigmaMin_le_frobNorm X Y
  rw [hX.measureReal_eq (p := fun A => sigmaMin A ≤ Real.sqrt N - Real.sqrt n - u)
    (measurableSet_le hc.measurable measurable_const)]
  exact measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix hn u hu

/-- `measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin N) (Fin n)) μ`. Atlas: `extreme-singular-values-deviation`. -/
theorem measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {N n : ℕ} {X : Ω → Matrix (Fin N) (Fin n) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin N) (Fin n)) μ) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | Real.sqrt N + Real.sqrt n + t ≤ specNorm (X ω)} ≤ Real.exp (-t ^ 2 / 2) := by
  have hc : Continuous (specNorm : Matrix (Fin N) (Fin n) ℝ → ℝ) :=
    continuous_of_abs_sub_le_mul_frobNorm specNorm 1 fun X Y => by
      rw [one_mul]; exact abs_specNorm_sub_specNorm_le_frobNorm X Y
  rw [hX.measureReal_eq (p := fun A => Real.sqrt N + Real.sqrt n + t ≤ specNorm A)
    (measurableSet_le measurable_const hc.measurable)]
  exact measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix t ht

/-- `one_sub_le_measure_sigmaMin_and_specNorm_gaussianMatrix` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin N) (Fin n)) μ`. Atlas: `extreme-singular-values-deviation`. -/
theorem one_sub_le_measure_sigmaMin_and_specNorm_gaussianMatrix_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {N n : ℕ} {X : Ω → Matrix (Fin N) (Fin n) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin N) (Fin n)) μ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    1 - 2 * Real.exp (-t ^ 2 / 2)
      ≤ μ.real {ω | Real.sqrt N - Real.sqrt n - t ≤ sigmaMin (X ω) ∧
          specNorm (X ω) ≤ Real.sqrt N + Real.sqrt n + t} := by
  have hs : Continuous (specNorm : Matrix (Fin N) (Fin n) ℝ → ℝ) :=
    continuous_of_abs_sub_le_mul_frobNorm specNorm 1 fun X Y => by
      rw [one_mul]; exact abs_specNorm_sub_specNorm_le_frobNorm X Y
  have hm : Continuous (sigmaMin : Matrix (Fin N) (Fin n) ℝ → ℝ) :=
    continuous_of_abs_sub_le_mul_frobNorm sigmaMin 1 fun X Y => by
      rw [one_mul]; exact abs_sigmaMin_sub_sigmaMin_le_frobNorm X Y
  rw [hX.measureReal_eq (p := fun A => Real.sqrt N - Real.sqrt n - t ≤ sigmaMin A ∧
      specNorm A ≤ Real.sqrt N + Real.sqrt n + t)
    ((measurableSet_le measurable_const hm.measurable).inter
      (measurableSet_le hs.measurable measurable_const))]
  exact one_sub_le_measure_sigmaMin_and_specNorm_gaussianMatrix hn t ht

end NLAlib
