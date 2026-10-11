import NLAlib.LowRank.Nystrom
import NLAlib.Matrix.SingletonInverse
import NLAlib.Matrix.GramVanishing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coordinate Cholesky residual pivots

A single coordinate pivot is the one-column Nyström residual. Its entrywise
formula and positive semidefinite order invariant are valid also at zero pivots.
Source: Chen--Epperly--Tropp--Webber (2025); manuscript `sa:rp-update`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The residual after one Cholesky coordinate pivot, with totalized zero-pivot
behavior. Source: manuscript `sa:rp-update`; CETW (2025), RPCholesky update. -/
def choleskyResidualStep (R : Matrix n n ℝ) (i : n) : Matrix n n ℝ :=
  R - nystrom R (fun (j : n) (_ : Fin 1) => if j = i then 1 else 0)

/-- A Cholesky coordinate pivot has the classical rank-one Schur-update formula.
Source: manuscript `sa:rp-update`; CETW (2025), RPCholesky update. -/
theorem choleskyResidualStep_apply (R : Matrix n n ℝ) (i j k : n) :
    choleskyResidualStep R i j k = R j k - R j i * (R i i)⁻¹ * R i k := by
  let E : Matrix n (Fin 1) ℝ := fun j _ => if j = i then 1 else 0
  have hcore : Eᵀ * R * E = Matrix.diagonal (fun _ : Fin 1 => R i i) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
    dsimp only [E]
    simp [ite_mul, mul_ite, Subsingleton.elim a b]
  change R j k - nystrom R E j k = _
  rw [nystrom, hcore, moorePenroseInverse_singleton]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one, Matrix.diagonal_apply]
  dsimp only [E]
  simp [ite_mul, mul_ite]

/-- Every Cholesky residual pivot preserves positive semidefiniteness, including a
zero diagonal pivot. Source: manuscript `sa:rp-one-step`; CETW (2025), PSD invariant. -/
theorem posSemidef_choleskyResidualStep {R : Matrix n n ℝ} (hR : R.PosSemidef) (i : n) :
    (choleskyResidualStep R i).PosSemidef :=
  posSemidef_sub_nystrom hR _

/-- The positive semidefinite Cholesky residual decreases in Loewner order.
Source: manuscript `sa:rp-one-step`; CETW (2025), PSD invariant. -/
theorem posSemidef_sub_choleskyResidualStep {R : Matrix n n ℝ} (hR : R.PosSemidef) (i : n) :
    (R - choleskyResidualStep R i).PosSemidef := by
  have he : R - choleskyResidualStep R i =
      nystrom R (fun (j : n) (_ : Fin 1) => if j = i then 1 else 0) := by
    unfold choleskyResidualStep
    abel
  rw [he]
  exact posSemidef_nystrom hR _

/-- A zero residual is absorbing for every pivot index.
Source: manuscript `sa:rp-update`, its absorbing-zero convention. -/
@[simp] theorem choleskyResidualStep_zero (i : n) :
    choleskyResidualStep (0 : Matrix n n ℝ) i = 0 := by
  ext j k
  simp [choleskyResidualStep_apply]

/-- A nonzero diagonal pivot eliminates its entire row.
Source: manuscript `sa:rp-update`, rank-termination argument. -/
theorem choleskyResidualStep_row_eq_zero {R : Matrix n n ℝ} {i : n}
    (hi : R i i ≠ 0) (j : n) : choleskyResidualStep R i i j = 0 := by
  rw [choleskyResidualStep_apply, mul_inv_cancel₀ hi, one_mul, sub_self]

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
    (∑ i, choleskyPivotProbability R i • choleskyResidualStep R i) =
      R - R.trace⁻¹ • (R * R) := by
  have hc : ∀ i j k, (R i i / R.trace) * (R j i * (R i i)⁻¹ * R i k) =
      R.trace⁻¹ * (R j i * R i k) := by
    intro i j k
    by_cases hi : R i i = 0
    · rw [hi, apply_eq_zero_of_posSemidef_of_diag_eq_zero hR hi j]
      simp
    · field_simp
  ext j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    choleskyResidualStep_apply, mul_sub, Finset.sum_sub_distrib, Matrix.sub_apply]
  have hp : ∑ i, choleskyPivotProbability R i * R j k = R j k := by
    rw [← Finset.sum_mul, sum_choleskyPivotProbability, one_mul]
  rw [hp]
  simp only [choleskyPivotProbability, if_neg ht, hc, ← Finset.mul_sum, Matrix.mul_apply]

/-- The finite expected trace after one randomly pivoted Cholesky step is
`tr R - tr(R²)/tr R`. Source: manuscript `sa:rp-one-step`; CETW (2025), one-step mean. -/
theorem sum_choleskyPivotProbability_mul_trace_step_eq [Nonempty n]
    {R : Matrix n n ℝ} (hR : R.PosSemidef) (ht : R.trace ≠ 0) :
    (∑ i, choleskyPivotProbability R i * (choleskyResidualStep R i).trace) =
      R.trace - (R * R).trace / R.trace := by
  have h := congrArg Matrix.trace (sum_choleskyPivotProbability_smul_step_eq hR ht)
  simpa only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_sub,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- A Cholesky residual pivot can only enlarge the kernel of the residual matrix.
Source: manuscript `sa:rp-rank`; CETW (2025), exhaustion of the column range. -/
theorem ker_mulVecLin_le_ker_choleskyResidualStep (R : Matrix n n ℝ) (i : n) :
    LinearMap.ker R.mulVecLin ≤ LinearMap.ker (choleskyResidualStep R i).mulVecLin := by
  let M : Matrix n n ℝ := fun j k => if k = i then R j i / R i i else 0
  have hfactor : choleskyResidualStep R i = (1 - M) * R := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    ext j k
    simp only [choleskyResidualStep_apply, Matrix.sub_apply, Matrix.mul_apply]
    simp only [M, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [div_eq_mul_inv]
  intro x hx
  change R *ᵥ x = 0 at hx
  change choleskyResidualStep R i *ᵥ x = 0
  rw [hfactor, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- Every positive diagonal Cholesky pivot strictly reduces rank. Source:
manuscript `sa:rp-rank`; CETW (2025), exact-rank exhaustion.
The proof adds the pivot coordinate to the kernel, so it does not require a
chosen basis of the residual range. -/
theorem rank_choleskyResidualStep_lt {R : Matrix n n ℝ} {i : n} (hi : R i i ≠ 0) :
    (choleskyResidualStep R i).rank < R.rank := by
  let e : n → ℝ := Pi.single i 1
  have hRe : R *ᵥ e ≠ 0 := by
    intro h
    have he := congrFun h i
    apply hi
    simpa only [e, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply, Pi.zero_apply] using he
  have hSe : choleskyResidualStep R i *ᵥ e = 0 := by
    dsimp only [e]
    rw [Matrix.mulVec_single_one]
    ext j
    change choleskyResidualStep R i j i = 0
    rw [choleskyResidualStep_apply, mul_assoc, inv_mul_cancel₀ hi, mul_one, sub_self]
  have hker : LinearMap.ker R.mulVecLin < LinearMap.ker (choleskyResidualStep R i).mulVecLin := by
    refine lt_of_le_of_ne (ker_mulVecLin_le_ker_choleskyResidualStep R i) ?_
    intro heq
    have he : e ∈ LinearMap.ker (choleskyResidualStep R i).mulVecLin := hSe
    rw [← heq] at he
    exact hRe he
  have hk := Submodule.finrank_lt_finrank_of_lt hker
  have hR := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
  have hS := LinearMap.finrank_range_add_finrank_ker (choleskyResidualStep R i).mulVecLin
  change R.rank + Module.finrank ℝ (LinearMap.ker R.mulVecLin) = _ at hR
  change (choleskyResidualStep R i).rank +
    Module.finrank ℝ (LinearMap.ker (choleskyResidualStep R i).mulVecLin) = _ at hS
  omega

end NLAlib
