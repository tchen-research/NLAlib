import NLAlib.RandomMatrix.Chaos.Flattenings
import NLAlib.ForMathlib.Combinatorics.ColoringAverage

/-!
# The exact finite coloring identity for multilinear matrix chaos

A coloring retains a term precisely when the color of each selected coordinate
equals its position. The diagonal-free support condition is the only coefficient
restriction; permutation symmetry is unnecessary.
Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, Theorem 2.1, upper direction.
-/

noncomputable section
open scoped Classical
namespace NLAlib

variable {τ ι m n : Type*} [Fintype τ] [Fintype ι] [DecidableEq τ] [DecidableEq ι]

/-- Retain exactly those chaos terms whose coordinate colors match their positions. -/
def coloredMatrixChaos (A : (τ → ι) → Matrix m n ℝ) (c : ι → τ) (h : ι → ℝ) :
    Matrix m n ℝ :=
  ∑ z, if ∀ t, c (z t) = t then (∏ t, h (z t)) • A z else 0

/-- A coefficient family is diagonal-free when every tuple with a repeated index
has zero coefficient. No permutation symmetry is part of this property. -/
def HasDistinctIndexSupport (A : (τ → ι) → Matrix m n ℝ) : Prop :=
  ∀ z, ¬ Function.Injective z → A z = 0

/-- Summing retained terms over all colorings and multiplying by `q^q` recovers
the number of colorings times the original chaos. This is a pointwise identity,
before any probabilistic argument.
Source: the finite coloring proof of matrix-chaos decoupling.
atlas: matrix-chaos-decoupling-upper (partial) -/
theorem card_pow_smul_sum_coloredMatrixChaos
    (A : (τ → ι) → Matrix m n ℝ) (hA : HasDistinctIndexSupport A) (h : ι → ℝ) :
    ((Fintype.card τ : ℝ) ^ Fintype.card τ) •
      (∑ c : ι → τ, coloredMatrixChaos A c h) =
        (Fintype.card (ι → τ) : ℝ) • coupledMatrixChaos A h := by
  simp only [coloredMatrixChaos, coupledMatrixChaos, decoupledMatrixChaos]
  rw [Finset.sum_comm, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : Function.Injective z
  · have hc : (∑ c : ι → τ, if ∀ t, c (z t) = t then (1 : ℝ) else 0) *
        (Fintype.card τ : ℝ) ^ Fintype.card τ = (Fintype.card (ι → τ) : ℝ) := by
      exact_mod_cast Finset.sum_coloring_indicator_mul_card_pow z hz
    have hs : (∑ c : ι → τ,
        if ∀ t, c (z t) = t then (∏ t, h (z t)) • A z else 0) =
        (∑ c : ι → τ, if ∀ t, c (z t) = t then (1 : ℝ) else 0) •
          ((∏ t, h (z t)) • A z) := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    rw [hs, smul_smul, mul_comm, hc]
  · simp [hA z hz]

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty τ]

open scoped Matrix.Norms.L2Operator in
/-- The coloring identity and triangle inequality give the first Jensen step of
one-sided decoupling, with the exact constant `q^q`.
Source: the finite coloring proof of matrix-chaos decoupling.
atlas: matrix-chaos-decoupling-upper (partial) -/
theorem specNorm_coupledMatrixChaos_le_coloring_average
    (A : (τ → ι) → Matrix m n ℝ) (hA : HasDistinctIndexSupport A) (h : ι → ℝ) :
    specNorm (coupledMatrixChaos A h) ≤
      (Fintype.card τ : ℝ) ^ Fintype.card τ /
        Fintype.card (ι → τ) * ∑ c, specNorm (coloredMatrixChaos A c h) := by
  have hc : 0 < (Fintype.card (ι → τ) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hq : 0 ≤ (Fintype.card τ : ℝ) ^ Fintype.card τ := by positivity
  have he := card_pow_smul_sum_coloredMatrixChaos A hA h
  have hn := congrArg (fun B : Matrix m n ℝ => ‖B‖) he
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hq,
    Real.norm_of_nonneg hc.le] at hn
  have hb : ‖∑ c, coloredMatrixChaos A c h‖ ≤
      ∑ c, ‖coloredMatrixChaos A c h‖ := norm_sum_le _ _
  simp_rw [specNorm_eq_norm]
  apply (mul_le_mul_iff_left₀ hc).mp
  calc
    ‖coupledMatrixChaos A h‖ * (Fintype.card (ι → τ) : ℝ) =
        (Fintype.card τ : ℝ) ^ Fintype.card τ * ‖∑ c, coloredMatrixChaos A c h‖ := by
          simpa [mul_comm] using hn.symm
    _ ≤ (Fintype.card τ : ℝ) ^ Fintype.card τ *
        (∑ c, ‖coloredMatrixChaos A c h‖) := mul_le_mul_of_nonneg_left hb hq
    _ = ((Fintype.card τ : ℝ) ^ Fintype.card τ /
        Fintype.card (ι → τ) * ∑ c, ‖coloredMatrixChaos A c h‖) *
        Fintype.card (ι → τ) := by field_simp

end NLAlib
