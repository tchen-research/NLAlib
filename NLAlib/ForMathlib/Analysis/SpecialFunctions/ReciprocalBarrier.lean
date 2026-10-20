import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

/-! # Reciprocal barrier averaging inequalities

Scalar gap estimates used by the barrier argument of Batson--Spielman--
Srivastava's deterministic rank-one sparsification (BSS).  For a finite
reciprocal sum `∑ᵢ 1/xᵢ` and a shift `δ > 0`, the two inequalities below
control the second-moment (squared reciprocal) contribution of one barrier
step by the linear reciprocal terms plus `1/δ`.  This file is the scalar
averaging part of the argument: the matrix trace decomposition, candidate
selection, and the full induction are out of scope.
Source: Batson--Spielman--Srivastava, *Twice-Ramanujan Sparsifiers* (2008),
Section 3.2 ([arXiv:0808.0163](https://arxiv.org/abs/0808.0163)).

## Main theorems

* `reciprocal_barrier_upper_le` — upper step: for `xᵢ > 0` and `δ > 0`,
  with `D = ∑ᵢ 1/xᵢ − ∑ᵢ 1/(xᵢ+δ) > 0`,
  `((∑ᵢ 1/(xᵢ+δ)²)/D) + ∑ᵢ 1/(xᵢ+δ) ≤ 1/δ + ∑ᵢ 1/xᵢ`.
* `reciprocal_barrier_lower_le` — lower step: for `δ > 0`, `yᵢ > δ`, and the
  potential bound `δ * ∑ᵢ 1/yᵢ ≤ 1`, with
  `D = ∑ᵢ 1/(yᵢ−δ) − ∑ᵢ 1/yᵢ > 0`,
  `1/δ − ∑ᵢ 1/yᵢ ≤ ((∑ᵢ 1/(yᵢ−δ)²)/D) − ∑ᵢ 1/(yᵢ−δ)`.
-/

noncomputable section
open scoped BigOperators

namespace Real

variable {I : Type*} [Fintype I]

/-- The reciprocal-barrier gap `∑ᵢ 1/xᵢ − ∑ᵢ 1/(xᵢ+δ)`. -/
def reciprocalBarrierGap (δ : ℝ) (x : I → ℝ) : ℝ :=
  (∑ i, 1 / x i) - ∑ i, 1 / (x i + δ)

private lemma inv_sq_le_inv_mul_inv_add {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    (1 / (x + δ)) ^ 2 ≤ 1 / (x * (x + δ)) := by
  rw [div_pow, one_pow]
  rw [div_le_div_iff₀ (pow_pos (add_pos hx hδ) 2) (mul_pos hx (add_pos hx hδ))]
  nlinarith [hx, hδ]

private lemma inv_add_lt_inv {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    1 / (x + δ) < 1 / x :=
  one_div_lt_one_div_of_lt hx (lt_add_of_pos_right x hδ)

/-- The reciprocal-barrier gap factors as `δ * ∑ᵢ 1/(xᵢ(xᵢ+δ))`. -/
theorem reciprocalBarrierGap_eq_mul_sum_inv_mul_inv_add {δ : ℝ} {x : I → ℝ}
    (hδ : 0 < δ) (hx : ∀ i, 0 < x i) :
    reciprocalBarrierGap δ x = δ * (∑ i, 1 / (x i * (x i + δ))) := by
  unfold reciprocalBarrierGap
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hxi : 0 < x i := hx i
  have hxiadd : 0 < x i + δ := add_pos hxi hδ
  field_simp [ne_of_gt hxi, ne_of_gt hxiadd, ne_of_gt (mul_pos hxi hxiadd)]
  ring

/-- The reciprocal-barrier gap is strictly positive for positive shifts and entries. -/
theorem reciprocalBarrierGap_pos [Nonempty I] {δ : ℝ} {x : I → ℝ}
    (hδ : 0 < δ) (hx : ∀ i, 0 < x i) : 0 < reciprocalBarrierGap δ x := by
  have hpos : 0 < ∑ i, 1 / (x i * (x i + δ)) := by
    exact Finset.sum_pos
      (fun i _ => one_div_pos.mpr (mul_pos (hx i) (add_pos (hx i) hδ)))
      Finset.univ_nonempty
  nlinarith [reciprocalBarrierGap_eq_mul_sum_inv_mul_inv_add hδ hx, hδ, hpos]

/-- Weighted Cauchy--Schwarz: `(∑ᵢ aᵢ bᵢ)² ≤ (∑ᵢ aᵢ) * (∑ᵢ aᵢ bᵢ²)`
when `aᵢ ≥ 0`. -/
private lemma sum_mul_sq_le_sum_mul_sum_mul_sq {a b : I → ℝ}
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i) * (∑ i, a i * (b i) ^ 2) := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => ha i)
    (fun i _ => mul_nonneg (ha i) (sq_nonneg (b i)))
    (fun i _ => by nlinarith [sq_nonneg (a i * b i)])
/-- Scalar upper reciprocal-barrier averaging inequality (BSS upper step).

For `δ > 0` and positive `xᵢ`, with
`D = ∑ᵢ 1/xᵢ − ∑ᵢ 1/(xᵢ+δ)`,
`((∑ᵢ 1/(xᵢ+δ)²)/D) + ∑ᵢ 1/(xᵢ+δ) ≤ 1/δ + ∑ᵢ 1/xᵢ`. -/
theorem reciprocal_barrier_upper_le [Nonempty I] {δ : ℝ} {x : I → ℝ}
    (hδ : 0 < δ) (hx : ∀ i, 0 < x i) :
    (((∑ i, (1 / (x i + δ)) ^ 2) /
        ((∑ i, 1 / x i) - ∑ i, 1 / (x i + δ))) +
      (∑ i, 1 / (x i + δ))) ≤
    1 / δ + (∑ i, 1 / x i) := by
  set S1 : ℝ := ∑ i, (1 / (x i + δ)) ^ 2 with hS1
  set S2 : ℝ := ∑ i, 1 / (x i * (x i + δ)) with hS2
  set S3 : ℝ := ∑ i, 1 / (x i + δ) with hS3
  set S4 : ℝ := ∑ i, 1 / x i with hS4
  set D : ℝ := S4 - S3 with hD
  have hxadd : ∀ i, 0 < x i + δ := fun i => add_pos (hx i) hδ
  have hS1_le_S2 : S1 ≤ S2 := by
    rw [hS1, hS2]
    exact Finset.sum_le_sum (fun i _ => inv_sq_le_inv_mul_inv_add (hx i) hδ)
  have hS3_le_S4 : S3 ≤ S4 := by
    rw [hS3, hS4]
    exact Finset.sum_le_sum (fun i _ => le_of_lt (inv_add_lt_inv (hx i) hδ))
  have hD_eq : D = δ * S2 := by
    rw [hD, hS4, hS3, hS2]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt (hx i), ne_of_gt (hxadd i),
      ne_of_gt (mul_pos (hx i) (hxadd i))]
    ring
  have hS2pos : 0 < S2 := by
    rw [hS2]
    exact Finset.sum_pos (fun i _ => one_div_pos.mpr (mul_pos (hx i) (hxadd i)))
      Finset.univ_nonempty
  have hDpos : 0 < D := by
    nlinarith [hD_eq, hδ, hS2pos]
  have hδS1 : δ * S1 ≤ δ * S2 := mul_le_mul_of_nonneg_left hS1_le_S2 hδ.le
  have hδDS3 : δ * D * S3 ≤ δ * D * S4 :=
    mul_le_mul_of_nonneg_left hS3_le_S4 (mul_pos hδ hDpos).le
  have hcleared : δ * S1 + δ * D * S3 ≤ D + δ * D * S4 := by
    nlinarith [hδS1, hδDS3, hD_eq]
  have hδD : 0 < δ * D := mul_pos hδ hDpos
  have hleft : (δ * S1 + δ * D * S3) / (δ * D) = S1 / D + S3 := by
    field_simp [hδ.ne', hDpos.ne']
  have hright : (D + δ * D * S4) / (δ * D) = 1 / δ + S4 := by
    field_simp [hδ.ne', hDpos.ne']
  calc
    S1 / D + S3 = (δ * S1 + δ * D * S3) / (δ * D) := by rw [hleft]
    _ ≤ (D + δ * D * S4) / (δ * D) := div_le_div_of_nonneg_right hcleared hδD.le
    _ = 1 / δ + S4 := by rw [hright]

/-- Scalar lower reciprocal-barrier averaging inequality (BSS lower step).

For `δ > 0`, `yᵢ > δ`, and the potential bound `δ * ∑ᵢ 1/yᵢ ≤ 1`,
with `D = ∑ᵢ 1/(yᵢ−δ) − ∑ᵢ 1/yᵢ`,
`1/δ − ∑ᵢ 1/yᵢ ≤ ((∑ᵢ 1/(yᵢ−δ)²)/D) − ∑ᵢ 1/(yᵢ−δ)`. -/
theorem reciprocal_barrier_lower_le [Nonempty I] {δ : ℝ} {y : I → ℝ}
    (hδ : 0 < δ) (hy : ∀ i, δ < y i) (hcap : δ * (∑ i, 1 / y i) ≤ 1) :
    1 / δ - (∑ i, 1 / y i) ≤
      ((∑ i, (1 / (y i - δ)) ^ 2) /
        ((∑ i, 1 / (y i - δ)) - ∑ i, 1 / y i)) -
      (∑ i, 1 / (y i - δ)) := by
  have hya : ∀ i, 0 < y i := fun i => lt_trans hδ (hy i)
  have ha : ∀ i, 0 < 1 / y i := fun i => one_div_pos.mpr (hya i)
  have hyb : ∀ i, 0 < y i - δ := fun i => sub_pos.mpr (hy i)
  have hb : ∀ i, 0 < 1 / (y i - δ) := fun i => one_div_pos.mpr (hyb i)
  set A : ℝ := ∑ i, 1 / y i with hA
  set B : ℝ := ∑ i, 1 / (y i - δ) with hB
  set E : ℝ := ∑ i, (1 / y i) * (1 / (y i - δ)) with hE
  set C : ℝ := ∑ i, (1 / y i) * (1 / (y i - δ)) ^ 2 with hC
  set B2 : ℝ := ∑ i, (1 / (y i - δ)) ^ 2 with hB2
  set D : ℝ := B - A with hD
  have hD_eq : D = δ * E := by
    rw [hD, hB, hA, hE]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt (hyb i), ne_of_gt (hya i)]
    ring
  have hBE : B2 - E = δ * C := by
    rw [hB2, hE, hC]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt (hyb i), ne_of_gt (hya i)]
    ring
  have hcauchy : E ^ 2 ≤ A * C := by
    rw [hE, hA, hC]
    exact sum_mul_sq_le_sum_mul_sum_mul_sq (fun i => (ha i).le)
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i).le (sq_nonneg _))
  have hEpos : 0 < E := by
    rw [hE]
    exact Finset.sum_pos (fun i _ => mul_pos (ha i) (hb i)) Finset.univ_nonempty
  have hDpos : 0 < D := by
    nlinarith [hD_eq, hδ, hEpos]
  have hδE2 : δ ^ 2 * E ^ 2 ≤ δ ^ 2 * (A * C) :=
    mul_le_mul_of_nonneg_left hcauchy (sq_nonneg δ)
  have hAC : δ * A * C ≤ C := by
    simpa using (mul_le_mul_of_nonneg_right hcap hCnonneg)
  have hδAC : δ * (δ * A * C) ≤ δ * C := mul_le_mul_of_nonneg_left hAC hδ.le
  have hDsq : D ^ 2 ≤ δ * C := by
    nlinarith [hD_eq, hδE2, hδAC]
  have hDpow : (δ * E) ^ 2 ≤ δ * C := by
    simpa [hD_eq] using hDsq
  have hDsq'' : δ ^ 3 * E ^ 2 ≤ δ ^ 2 * C := by
    nlinarith [mul_le_mul_of_nonneg_left hDpow hδ.le]
  have hBA : B - A = δ * E := hD.symm.trans hD_eq
  have hcleared : D - δ * A * D ≤ δ * B2 - δ * D * B := by
    rw [hD_eq]
    nlinarith [hBE, hBA, hDsq'', hδ]
  have hδD : 0 < δ * D := mul_pos hδ hDpos
  have hleft : (δ * B2 - δ * D * B) / (δ * D) = B2 / D - B := by
    field_simp [hδ.ne', hDpos.ne']
  have hright : (D - δ * A * D) / (δ * D) = 1 / δ - A := by
    field_simp [hδ.ne', hDpos.ne']
  calc
    1 / δ - A = (D - δ * A * D) / (δ * D) := by rw [hright]
    _ ≤ (δ * B2 - δ * D * B) / (δ * D) := div_le_div_of_nonneg_right hcleared hδD.le
    _ = B2 / D - B := by rw [hleft]

end Real
