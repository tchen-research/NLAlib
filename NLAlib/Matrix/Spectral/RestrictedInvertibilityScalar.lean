import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar weighted lower-barrier estimate

This is the scalar inequality in the weighted lower-barrier proof of
Spielman--Srivastava (2009), Theorem 2. It retains the mass on the kernel;
positive eigenvalues and zero eigenvalues contribute different reciprocal
estimates. It is used for stable-rank restricted invertibility.
-/

noncomputable section

open scoped BigOperators

namespace NLAlib.RestrictedInvertibility

variable {ι : Type*} [Fintype ι]

/-- A positive spectral value above the old barrier contributes a nonnegative
reciprocal gap and dominates the new squared reciprocal after multiplication
by the barrier decrement. -/
theorem reciprocal_gap_nonneg_and_sq_le {a b δ : ℝ}
    (ha : b < a) (hδ : 0 < δ) :
    0 ≤ 1 / (a - b) - 1 / (a - (b - δ)) ∧
      δ / (a - (b - δ)) ^ 2 ≤
        1 / (a - b) - 1 / (a - (b - δ)) := by
  have hx : 0 < a - b := sub_pos.mpr ha
  have hy : 0 < a - (b - δ) := by linarith
  have hid : 1 / (a - b) - 1 / (a - (b - δ)) =
      δ / ((a - b) * (a - (b - δ))) := by
    field_simp
    ring
  rw [hid]
  constructor
  · positivity
  · apply (div_le_div_iff₀ (sq_pos_of_pos hy) (mul_pos hx hy)).mpr
    nlinarith [mul_nonneg hδ.le (mul_nonneg hy.le hδ.le)]

/-- The kernel reciprocal gap has the exact value `δ / (b * (b - δ))`. -/
theorem zero_reciprocal_gap {b δ : ℝ} (hδ : 0 < δ) (hb : δ < b) :
    1 / (0 - b) - 1 / (0 - (b - δ)) = δ / (b * (b - δ)) := by
  have hb0 : b ≠ 0 := ne_of_gt (lt_trans hδ hb)
  have hb' : b - δ ≠ 0 := ne_of_gt (sub_pos.mpr hb)
  field_simp
  ring

/-- Weighted scalar lower-barrier estimate, including the kernel contribution.
If each spectral value is zero or above `b`, the kernel mass is `q`, and
`b * Λ ≤ δ * q`, then the squared new resolvent is bounded by the actual
weighted reciprocal gap. This is the quantitative averaging inequality in
Spielman--Srivastava (2009), Theorem 2. -/
theorem weighted_reciprocal_sq_le
    (a w : ι → ℝ) {b δ Λ : ℝ} (hδ : 0 < δ) (hb : δ < b)
    (hΛ : 0 < Λ) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, a i = 0 ∨ b < a i)
    (hkernel : b * Λ ≤ δ * ∑ i, if a i = 0 then w i else 0) :
    let Δ := ∑ i, w i * (1 / (a i - b) - 1 / (a i - (b - δ)))
    0 < Δ ∧
      Λ * (∑ i, w i / (a i - (b - δ)) ^ 2) ≤ Δ * (Λ / δ + Δ) := by
  classical
  let q : ℝ := ∑ i, if a i = 0 then w i else 0
  let Δ : ℝ := ∑ i, w i * (1 / (a i - b) - 1 / (a i - (b - δ)))
  let z : ℝ := δ * q / (b * (b - δ))
  have hb0 : 0 < b := lt_trans hδ hb
  have hb' : 0 < b - δ := sub_pos.mpr hb
  have hq : 0 < q := by
    have hh : 0 < δ * q := lt_of_lt_of_le (mul_pos hb0 hΛ) hkernel
    exact pos_of_mul_pos_right hh hδ.le
  have hz : 0 < z := by dsimp [z]; positivity
  have hgap (i : ι) : 0 ≤ 1 / (a i - b) - 1 / (a i - (b - δ)) := by
    rcases ha i with hi | hi
    · rw [hi, zero_reciprocal_gap hδ hb]
      positivity
    · exact (reciprocal_gap_nonneg_and_sq_le hi hδ).1
  have hzle : z ≤ Δ := by
    calc
      z = ∑ i, if a i = 0 then
          w i * (1 / (a i - b) - 1 / (a i - (b - δ))) else 0 := by
        simp only [z, q, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · rw [hi, zero_reciprocal_gap hδ hb]
          ring
        · ring
      _ ≤ Δ := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hw i) (hgap i)
  have hΔ : 0 < Δ := hz.trans_le hzle
  have hpoint (i : ι) :
      δ * (w i / (a i - (b - δ)) ^ 2) ≤
        w i * (1 / (a i - b) - 1 / (a i - (b - δ))) +
          if a i = 0 then δ ^ 2 * w i / (b * (b - δ) ^ 2) else 0 := by
    by_cases hi : a i = 0
    · rw [if_pos hi, hi, zero_reciprocal_gap hδ hb]
      have hbne := ne_of_gt hb0
      have hbne' := ne_of_gt hb'
      apply le_of_eq
      field_simp
      ring
    · rw [if_neg hi, add_zero]
      have hab := (ha i).resolve_left hi
      have hh := mul_le_mul_of_nonneg_left
        (reciprocal_gap_nonneg_and_sq_le hab hδ).2 (hw i)
      calc
        δ * (w i / (a i - (b - δ)) ^ 2) =
            w i * (δ / (a i - (b - δ)) ^ 2) := by ring
        _ ≤ _ := hh
  have hsum : δ * (∑ i, w i / (a i - (b - δ)) ^ 2) ≤
      Δ + δ ^ 2 * q / (b * (b - δ) ^ 2) := by
    calc
      δ * (∑ i, w i / (a i - (b - δ)) ^ 2) ≤
          ∑ i, (w i * (1 / (a i - b) - 1 / (a i - (b - δ))) +
            if a i = 0 then δ ^ 2 * w i / (b * (b - δ) ^ 2) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hpoint i
      _ = Δ + δ ^ 2 * q / (b * (b - δ) ^ 2) := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [q, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
  have hk : Λ * (δ ^ 2 * q / (b * (b - δ) ^ 2)) ≤ δ * z ^ 2 := by
    dsimp [z]
    have hh := mul_le_mul_of_nonneg_right hkernel
      (show 0 ≤ δ ^ 2 * q / (b ^ 2 * (b - δ) ^ 2) by positivity)
    calc
      Λ * (δ ^ 2 * q / (b * (b - δ) ^ 2)) =
          (b * Λ) * (δ ^ 2 * q / (b ^ 2 * (b - δ) ^ 2)) := by
        field_simp
      _ ≤ (δ * q) * (δ ^ 2 * q / (b ^ 2 * (b - δ) ^ 2)) := hh
      _ = δ * (δ * q / (b * (b - δ))) ^ 2 := by
        field_simp
  have hzsq : z ^ 2 ≤ Δ ^ 2 := sq_le_sq₀ hz.le hΔ.le |>.mpr hzle
  refine ⟨hΔ, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hsum hΛ.le
  have hright := mul_le_mul_of_nonneg_left hzsq hδ.le
  have hfinal : δ * (Λ * (∑ i, w i / (a i - (b - δ)) ^ 2)) ≤
      δ * (Δ * (Λ / δ + Δ)) := by
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have heq : δ * (Δ * (Λ / δ + Δ)) = Λ * Δ + δ * Δ ^ 2 := by
      field_simp
    rw [heq]
    nlinarith
  exact (mul_le_mul_iff_right₀ hδ).mp hfinal

end NLAlib.RestrictedInvertibility
