import NLAlib.LowRank.Nystrom.Structural
import NLAlib.Matrix.Basic.SingletonInverse
import NLAlib.Matrix.Basic.GramVanishing
import NLAlib.Matrix.Factorizations.CholeskyStep

/-!
# Coordinate Cholesky residual pivots

A single coordinate pivot `choleskyStep` (Matrix/Factorizations/CholeskyStep) is the one-column
Nyström residual (`choleskyStep_eq_sub_nystrom`), also at zero pivots. The diagonal-over-trace
pivot probabilities `choleskyPivotProbability` give the one-step means of RPCholesky.
Source: Chen--Epperly--Tropp--Webber (2025); manuscript `sa:rp-update`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Cholesky coordinate pivot is the one-column Nyström residual:
`choleskyStep R i = R − nystrom R eᵢ`, including at a zero pivot (both sides are then `R`).
Source: manuscript `sa:rp-update`; CETW (2025), RPCholesky update. -/
theorem choleskyStep_eq_sub_nystrom (R : Matrix n n ℝ) (i : n) :
    choleskyStep R i = R - nystrom R (fun (j : n) (_ : Fin 1) => if j = i then 1 else 0) := by
  let E : Matrix n (Fin 1) ℝ := fun j _ => if j = i then 1 else 0
  have hcore : Eᵀ * R * E = Matrix.diagonal (fun _ : Fin 1 => R i i) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
    dsimp only [E]
    simp [ite_mul, mul_ite, Subsingleton.elim a b]
  ext j k
  rw [choleskyStep_apply]
  change _ = R j k - nystrom R E j k
  rw [nystrom, hcore, moorePenroseInverse_singleton]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one, Matrix.diagonal_apply]
  dsimp only [E]
  simp [ite_mul, mul_ite]
  ring

omit [DecidableEq n] in
/-- Diagonal-over-trace pivot probabilities, with a uniform absorbing-state choice.
Source: manuscript `sa:rp-update`; CETW (2025), RPCholesky pivot law. -/
def choleskyPivotProbability (R : Matrix n n ℝ) (i : n) : ℝ :=
  if R.trace = 0 then 1 / (Fintype.card n : ℝ) else R i i / R.trace

omit [DecidableEq n] in
/-- The diagonal pivot probabilities sum to one, including the absorbing zero state.
Source: manuscript `sa:rp-update`; CETW (2025), pivot law normalization. -/
theorem sum_choleskyPivotProbability [Nonempty n] (R : Matrix n n ℝ) :
    ∑ i, choleskyPivotProbability R i = 1 := by
  by_cases ht : R.trace = 0
  · simp only [choleskyPivotProbability, if_pos ht, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero)
  · simp only [choleskyPivotProbability, if_neg ht, ← Finset.sum_div]
    exact div_self ht

omit [DecidableEq n] in
/-- Positive semidefinite residuals give nonnegative pivot probabilities.
Source: manuscript `sa:rp-update`; CETW (2025), finite transition law. -/
theorem choleskyPivotProbability_nonneg {R : Matrix n n ℝ} (hR : R.PosSemidef) (i : n) :
    0 ≤ choleskyPivotProbability R i := by
  unfold choleskyPivotProbability
  split_ifs
  · positivity
  · exact div_nonneg hR.diag_nonneg (Finset.sum_nonneg fun j _ => hR.diag_nonneg)

/-- The finite expected matrix after one randomly pivoted Cholesky step is
`R - R² / tr R`. Source: manuscript `sa:rp-one-step`; CETW (2025), one-step mean.
Zero diagonal indices are handled using their vanishing Gram columns. -/
theorem sum_choleskyPivotProbability_smul_step_eq [Nonempty n]
    {R : Matrix n n ℝ} (hR : R.PosSemidef) (ht : R.trace ≠ 0) :
    (∑ i, choleskyPivotProbability R i • choleskyStep R i) =
      R - R.trace⁻¹ • (R * R) := by
  have hc : ∀ i j k, (R i i / R.trace) * ((R i i)⁻¹ * (R j i * R i k)) =
      R.trace⁻¹ * (R j i * R i k) := by
    intro i j k
    by_cases hi : R i i = 0
    · rw [hi, apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hR hi j]
      simp
    · field_simp
  ext j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    choleskyStep_apply, mul_sub, Finset.sum_sub_distrib, Matrix.sub_apply]
  have hp : ∑ i, choleskyPivotProbability R i * R j k = R j k := by
    rw [← Finset.sum_mul, sum_choleskyPivotProbability, one_mul]
  rw [hp]
  simp only [choleskyPivotProbability, if_neg ht, hc, ← Finset.mul_sum, Matrix.mul_apply]

/-- The finite expected trace after one randomly pivoted Cholesky step is
`tr R - tr(R²)/tr R`, also at the absorbing zero state (totalized division by zero).
Source: manuscript `sa:rp-one-step` and `sa:rp-recursion`; CETW (2025), one-step mean. -/
theorem sum_choleskyPivotProbability_mul_trace_step_eq [Nonempty n]
    {R : Matrix n n ℝ} (hR : R.PosSemidef) :
    (∑ i, choleskyPivotProbability R i * (choleskyStep R i).trace) =
      R.trace - (R * R).trace / R.trace := by
  by_cases ht : R.trace = 0
  · have hzero : R = 0 := hR.trace_eq_zero_iff.mp ht
    rw [hzero]
    simp only [choleskyStep_zero, Matrix.trace_zero, mul_zero, Finset.sum_const_zero,
      div_zero, sub_self]
  · have h := congrArg Matrix.trace (sum_choleskyPivotProbability_smul_step_eq hR ht)
    simpa only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_sub,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end NLAlib
