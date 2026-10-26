import NLAlib.Matrix.Functions.ReciprocalBarrier
import Mathlib.Algebra.BigOperators.Fin

/-!
# Resolvent trace after deleting a principal coordinate

Deleting coordinate `j` from an invertible matrix changes the inverse trace
by `(R²)jj / Rjj`, where `R` is the original inverse. The identity is proved
by multiplying the explicit Schur-complement inverse; no conditional
spectral-selection assumption is used.
-/

noncomputable section

open scoped Matrix BigOperators
open Matrix

namespace NLAlib.RestrictedInvertibility

/-- Exact inverse-trace identity after deleting one principal coordinate.
The sole extra denominator is the corresponding diagonal entry of the full
inverse. The result also includes deletion from a one-by-one matrix. -/
theorem trace_inv_submatrix_succAbove_eq {q : ℕ}
    (M : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (hM : IsUnit M)
    (j : Fin (q + 1)) (hjj : M⁻¹ j j ≠ 0) :
    (M.submatrix j.succAbove j.succAbove)⁻¹.trace =
      M⁻¹.trace - (M⁻¹ ^ 2) j j / M⁻¹ j j := by
  let R : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ := M⁻¹
  let N : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
    fun a b => R a b - R a j * R j b / R j j
  have hMR : M * R = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM)
  have hNj (b : Fin (q + 1)) : N j b = 0 := by
    dsimp [N]
    field_simp [show R j j ≠ 0 from hjj]
    ring
  have hfull (a b : Fin (q + 1)) :
      (∑ l, M a l * N l b) = (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) a b -
        (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) a j * R j b / R j j := by
    have hab := congrArg (fun P : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ => P a b) hMR
    have haj := congrArg (fun P : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ => P a j) hMR
    change (∑ l, M a l * R l b) = _ at hab
    change (∑ l, M a l * R l j) = _ at haj
    calc
      _ = (∑ l, M a l * R l b) - (∑ l, M a l * R l j) * R j b / R j j := by
        dsimp [N]
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div]
        apply congrArg₂ (· - ·) rfl
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [hab, haj]
  have hinv : (M.submatrix j.succAbove j.succAbove)⁻¹ =
      N.submatrix j.succAbove j.succAbove := by
    apply Matrix.inv_eq_right_inv
    ext a b
    change (∑ l : Fin q, M (j.succAbove a) (j.succAbove l) *
      N (j.succAbove l) (j.succAbove b)) = (1 : Matrix (Fin q) (Fin q) ℝ) a b
    have hs := Fin.sum_univ_succAbove
      (fun l => M (j.succAbove a) l * N l (j.succAbove b)) j
    rw [hNj, mul_zero, zero_add, hfull] at hs
    have hne := j.succAbove_ne a
    have heq : (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (j.succAbove a) (j.succAbove b) =
        (1 : Matrix (Fin q) (Fin q) ℝ) a b := by
      exact congrArg (fun P : Matrix (Fin q) (Fin q) ℝ => P a b)
        (Matrix.submatrix_one j.succAbove Fin.succAbove_right_injective)
    simpa only [Matrix.one_apply_ne hne, zero_mul, zero_div, sub_zero, heq] using hs.symm
  rw [hinv]
  have hs := Fin.sum_univ_succAbove (fun a => N a a) j
  rw [hNj, zero_add] at hs
  change (∑ a : Fin q, N (j.succAbove a) (j.succAbove a)) = _
  rw [← hs]
  dsimp [N]
  rw [Finset.sum_sub_distrib]
  change R.trace - (∑ a, R a j * R j a / R j j) = R.trace - (R ^ 2) j j / R j j
  congr 1
  rw [← Finset.sum_div, pow_two, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- Moving a positive definite lower barrier by `δ`, then deleting a suitable
coordinate, preserves a fixed inverse-trace budget `T` whenever `2δT ≤ 1`.
All principal submatrices of the shifted matrix are positive definite. -/
theorem exists_principal_deletion_posDef_and_trace_inv_le {q : ℕ}
    {M : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ} (hM : M.PosDef)
    {δ T : ℝ} (hδ : 0 < δ) (_hT : 0 < T) (htrace : M⁻¹.trace ≤ T)
    (hstep : 2 * δ * T ≤ 1) :
    ∃ j : Fin (q + 1),
      ((M - δ • (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)).submatrix
        j.succAbove j.succAbove).PosDef ∧
      ((M - δ • (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)).submatrix
        j.succAbove j.succAbove)⁻¹.trace ≤ T := by
  have hcap : δ * M⁻¹.trace < 1 := by
    have hh := mul_le_mul_of_nonneg_left htrace hδ.le
    nlinarith
  let S := M - δ • (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)
  let R := S⁻¹
  have hS : S.PosDef := hM.sub_smul_one_posDef_of_mul_trace_inv_lt_one hδ hcap
  have hR : R.PosDef := hS.inv
  have hgap : 0 < R.trace - M⁻¹.trace := hM.trace_sub_smul_one_inv_sub_trace_inv_pos hδ hcap
  have havg := hM.reciprocal_barrier_lower_le hδ hcap
  change 1 / δ - M⁻¹.trace ≤ (R ^ 2).trace / (R.trace - M⁻¹.trace) - R.trace at havg
  have hsq : (1 / δ - M⁻¹.trace + R.trace) * (R.trace - M⁻¹.trace) ≤ (R ^ 2).trace :=
    (le_div_iff₀ hgap).mp (by linarith)
  have hδT : δ * T ≤ 1 := by nlinarith
  have hTδ : T ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hnon : 0 ≤ M⁻¹.trace := hM.inv.posSemidef.trace_nonneg
  have hRtrace : 0 < R.trace := hR.trace_pos
  have hquad : R.trace * (R.trace - T) ≤ (R ^ 2).trace := by
    have hd : 0 ≤ T - M⁻¹.trace := sub_nonneg.mpr htrace
    have hprod := mul_nonneg (sub_nonneg.mpr hTδ) hgap.le
    have hprod' := mul_nonneg hd hnon
    have hprod'' := mul_nonneg hd hgap.le
    nlinarith
  have hsum : (∑ j, R j j * (R.trace - T)) ≤ ∑ j, (R ^ 2) j j := by
    simpa only [← Finset.sum_mul, Matrix.trace, Matrix.diag] using hquad
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨j, hS.submatrix Fin.succAbove_right_injective, ?_⟩
  rw [trace_inv_submatrix_succAbove_eq S hS.isUnit j (ne_of_gt (hR.diag_pos (i := j)))]
  change R.trace - (R ^ 2) j j / R j j ≤ T
  have hdiv : R.trace - T ≤ (R ^ 2) j j / R j j :=
    (le_div_iff₀ (hR.diag_pos (i := j))).mpr (by nlinarith [hj])
  linarith

end NLAlib.RestrictedInvertibility
