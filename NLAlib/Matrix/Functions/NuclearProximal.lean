/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Functions.SingularValueTransform
import NLAlib.Matrix.Norms.NuclearConvexity
import Mathlib.Tactic.Module

/-! # Singular-value soft thresholding is the nuclear proximal map

The scalar quadratic-plus-linear objective is minimized at the positive-part cutoff.
Von Neumann's trace inequality transfers this comparison to matrices, and strict
Frobenius convexity gives uniqueness of the matrix minimizer, including threshold zero.
Source: Cai–Candès–Shen (2010), Theorem 2.1.
Atlas: `nuclear-norm-proximal`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The nuclear-penalized squared-error objective, with its exact normalization. -/
def nuclearProxObjective (τ : ℝ) (Y X : Matrix m n 𝕜) : ℝ :=
  1 / 2 * frobSq (X - Y) + τ * nuclearNorm X

private theorem softThreshold_scalar_objective_le {x y τ : ℝ}
    (hx : 0 ≤ x) :
    1 / 2 * (max (y - τ) 0 - y) ^ 2 + τ * max (y - τ) 0 ≤
      1 / 2 * (x - y) ^ 2 + τ * x := by
  by_cases h : τ ≤ y
  · rw [max_eq_left (sub_nonneg.mpr h)]
    nlinarith [sq_nonneg (x - (y - τ))]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    nlinarith [sq_nonneg x, mul_nonneg hx (sub_nonneg.mpr (le_of_not_ge h))]

private theorem sum_softThreshold_objective {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) (τ : ℝ) :
    (∑ i ∈ s, (1 / 2 * (x i - y i) ^ 2 + τ * x i)) =
      1 / 2 * (∑ i ∈ s, x i ^ 2) - (∑ i ∈ s, x i * y i) +
        1 / 2 * (∑ i ∈ s, y i ^ 2) + τ * ∑ i ∈ s, x i := by
  calc
    _ = ∑ i ∈ s, (1 / 2 * x i ^ 2 - x i * y i + 1 / 2 * y i ^ 2 + τ * x i) :=
      Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

omit [DecidableEq m] in
private theorem singular_value_objective_le (τ : ℝ) (Y X : Matrix m n 𝕜) :
    (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      (1 / 2 * (singularValues X i - singularValues Y i) ^ 2 + τ * singularValues X i)) ≤
        nuclearProxObjective τ Y X := by
  rw [sum_softThreshold_objective, nuclearProxObjective, frobSq_sub,
    frobSq_eq_sum_sq_singularValues X, frobSq_eq_sum_sq_singularValues Y,
    nuclearNorm_eq_sum_range]
  have h := frobInner_le_sum_singularValues_mul X Y
  linarith

private theorem nuclearProxObjective_softThreshold_eq (Y : Matrix m n 𝕜)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    nuclearProxObjective τ Y (singularValueSoftThreshold τ Y) =
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        (1 / 2 * (max (singularValues Y i - τ) 0 - singularValues Y i) ^ 2 +
          τ * max (singularValues Y i - τ) 0) := by
  obtain ⟨U, V, h⟩ := exists_isSVD Y
  have hInner : frobInner (singularValueSoftThreshold τ Y) Y =
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        max (singularValues Y i - τ) 0 * singularValues Y i := by
    rw [frobInner_comm, h.singularValueSoftThreshold_eq hτ,
      h.frobInner_mul_rectDiag_mul_conjTranspose]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [nuclearProxObjective, frobSq_sub, hInner,
    frobSq_eq_sum_sq_singularValues, frobSq_eq_sum_sq_singularValues,
    nuclearNorm_eq_sum_range, sum_softThreshold_objective]
  simp only [singularValues_singularValueSoftThreshold Y hτ]
  ring

/-- Soft thresholding globally minimizes the nuclear proximal objective over real or
complex matrices, including `τ=0`, empty dimensions, and repeated singular values.
Cai–Candès–Shen (2010), Theorem 2.1.
atlas: nuclear-norm-proximal (partial) -/
theorem nuclearProxObjective_softThreshold_le (Y X : Matrix m n 𝕜)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    nuclearProxObjective τ Y (singularValueSoftThreshold τ Y) ≤ nuclearProxObjective τ Y X := by
  rw [nuclearProxObjective_softThreshold_eq Y hτ]
  exact (Finset.sum_le_sum fun i _ =>
    softThreshold_scalar_objective_le (singularValues_nonneg X i)).trans
      (singular_value_objective_le τ Y X)

omit [DecidableEq m] [DecidableEq n] in
private theorem frobSq_midpoint (A B : Matrix m n 𝕜) :
    frobSq ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B) =
      1 / 2 * frobSq A + 1 / 2 * frobSq B - 1 / 4 * frobSq (A - B) := by
  rw [frobSq_add, frobSq_smul, frobSq_smul, frobInner_smul_left,
    frobInner_smul_right, frobSq_sub]
  ring

/-- The matrix minimizer of the nuclear proximal objective is unique. This follows from
strict Frobenius convexity rather than an equality-case assertion about singular vectors.
Cai–Candès–Shen (2010), Theorem 2.1.
atlas: nuclear-norm-proximal (partial) -/
theorem eq_singularValueSoftThreshold_of_nuclearProxObjective_le (Y X : Matrix m n 𝕜)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hX : nuclearProxObjective τ Y X ≤
      nuclearProxObjective τ Y (singularValueSoftThreshold τ Y)) :
    X = singularValueSoftThreshold τ Y := by
  let D := singularValueSoftThreshold τ Y
  let M := (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • D
  have hMid := nuclearProxObjective_softThreshold_le Y M hτ
  have hNuc := (convexOn_nuclearNorm (𝕜 := 𝕜) (m := m) (n := n)).2
    (show X ∈ Set.univ from Set.mem_univ X) (show D ∈ Set.univ from Set.mem_univ D)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hM : M - Y = (1 / 2 : ℝ) • (X - Y) + (1 / 2 : ℝ) • (D - Y) := by
    dsimp [M]
    module
  have hDiff : (X - Y) - (D - Y) = X - D := by abel
  have hQuad : frobSq (M - Y) =
      1 / 2 * frobSq (X - Y) + 1 / 2 * frobSq (D - Y) - 1 / 4 * frobSq (X - D) := by
    rw [hM, frobSq_midpoint, hDiff]
  have hNuc' := mul_le_mul_of_nonneg_left hNuc hτ
  change nuclearNorm M ≤ _ at hNuc
  change nuclearProxObjective τ Y D ≤ nuclearProxObjective τ Y M at hMid
  change nuclearProxObjective τ Y X ≤ nuclearProxObjective τ Y D at hX
  have hSq : frobSq (X - D) ≤ 0 := by
    unfold nuclearProxObjective at hMid hX
    rw [hQuad] at hMid
    change τ * nuclearNorm M ≤ τ * (1 / 2 * nuclearNorm X + 1 / 2 * nuclearNorm D) at hNuc'
    nlinarith
  exact sub_eq_zero.mp ((frobSq_eq_zero_iff _).mp (le_antisymm hSq (frobSq_nonneg _)))

/-- The nuclear-norm proximal map is exactly singular-value soft thresholding, with a
unique matrix minimizer over either scalar field and all nonnegative thresholds.
Cai–Candès–Shen (2010), Theorem 2.1.
atlas: nuclear-norm-proximal -/
theorem nuclearProxObjective_minimizer_iff (Y X : Matrix m n 𝕜)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ Z, nuclearProxObjective τ Y X ≤ nuclearProxObjective τ Y Z) ↔
      X = singularValueSoftThreshold τ Y := by
  constructor
  · intro h
    exact eq_singularValueSoftThreshold_of_nuclearProxObjective_le Y X hτ (h _)
  · rintro rfl
    exact fun Z => nuclearProxObjective_softThreshold_le Y Z hτ

end NLAlib
