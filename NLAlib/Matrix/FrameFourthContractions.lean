import NLAlib.Matrix.Projections
import NLAlib.ForMathlib.Algebra.DiagonalSums

/-!
# Fourth-order contractions of an orthonormal frame

The two contractions from the CountSketch sign moment total `d²` and `d`.
Removing their equal-index terms subtracts twice the sum of squared row
energies. Source: operator manuscript `sh:parseval`, `sh:count-second`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Matrix
namespace NLAlib

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

omit [Fintype d] [DecidableEq ι] in
/-- Column cross-products of a real orthonormal frame form the identity.
Source: the Gram identity; supports `sparse-ose` fourth-order contractions. -/
theorem sum_mul_columns_eq_one_apply (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U)
    (a b : d) : ∑ i, U i a * U i b = (1 : Matrix d d ℝ) a b := by
  have h := congrFun (congrFun hU a) b
  simpa only [Matrix.mul_apply, Matrix.transpose_apply] using h

omit [Fintype d] [DecidableEq ι] in
/-- The independent row-energy contraction of two columns is one.
Source: the orthonormal-column identity; supports `sparse-ose`. -/
theorem sum_sum_sq_mul_columns_eq_one (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U)
    (a b : d) : ∑ i, ∑ j, (U i a * U j b) ^ 2 = 1 := by
  have hcol (c : d) : ∑ i, U i c ^ 2 = 1 := by
    simpa only [pow_two, Matrix.one_apply_eq] using sum_mul_columns_eq_one_apply U hU c c
  simp_rw [mul_pow]
  rw [← Finset.sum_mul_sum, hcol, hcol, one_mul]

omit [Fintype d] [DecidableEq ι] in
/-- The crossed fourth-order contraction of two columns equals the square
of the identity's corresponding Gram entry. Source: the frame Gram identity;
supports CountSketch `sparse-ose`. -/
theorem sum_sum_mul_cross_columns_eq_one_sq
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) (a b : d) :
    (∑ i, ∑ j, (U i a * U j b) * (U j a * U i b)) =
      ((1 : Matrix d d ℝ) a b) ^ 2 := by
  calc
    _ = (∑ i, U i a * U i b) * (∑ j, U j a * U j b) := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = _ := by rw [sum_mul_columns_eq_one_apply U hU, pow_two]

omit [DecidableEq ι] [DecidableEq d] in
/-- Summing the equal-row fourth powers over the column pair gives the
sum of squared row energies. Source: finite products of sums in manuscript
`sh:count-second`; supports `sparse-ose`. -/
theorem sum_sum_sum_sq_row_mul_eq_sum_row_energy_sq (U : Matrix ι d ℝ) :
    (∑ a, ∑ b, ∑ i, (U i a * U i b) ^ 2) =
      ∑ i, (∑ a, U i a ^ 2) ^ 2 := by
  calc
    _ = ∑ a, ∑ i, ∑ b, (U i a * U i b) ^ 2 := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, (U i a * U i b) ^ 2 := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp_rw [mul_pow]
      rw [← Finset.sum_mul_sum, pow_two]

/-- The two off-diagonal fourth-order frame contractions total exactly
`d²+d−2∑ rowEnergy²`. Source: manuscript `sh:count-second`;
supports the sharp CountSketch second moment in `sparse-ose`. -/
theorem sum_offDiagonal_frame_contractions_eq
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) :
    (∑ a, ∑ b, ∑ i, ∑ j, if i = j then 0 else
      (U i a * U j b) ^ 2 + (U i a * U j b) * (U j a * U i b)) =
      (Fintype.card d : ℝ) ^ 2 + Fintype.card d -
        2 * ∑ i, (∑ a, U i a ^ 2) ^ 2 := by
  have hoff (a b : d) :
      (∑ i, ∑ j, if i = j then 0 else
        (U i a * U j b) ^ 2 + (U i a * U j b) * (U j a * U i b)) =
      1 + ((1 : Matrix d d ℝ) a b) ^ 2 - 2 * ∑ i, (U i a * U i b) ^ 2 := by
    rw [sum_sum_ite_ne_eq_sub_diag (fun (i j : ι) =>
      (U i a * U j b) ^ 2 + (U i a * U j b) * (U j a * U i b))]
    simp only [Finset.sum_add_distrib]
    rw [sum_sum_sq_mul_columns_eq_one U hU, sum_sum_mul_cross_columns_eq_one_sq U hU]
    have hdiag : (∑ i, ((U i a * U i b) ^ 2 + (U i a * U i b) * (U i a * U i b))) =
        2 * ∑ i, (U i a * U i b) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [Finset.sum_add_distrib] at hdiag
    rw [hdiag]
  simp_rw [hoff, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_sum_sum_sq_row_mul_eq_sum_row_energy_sq]
  simp only [Matrix.one_apply, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

end NLAlib
