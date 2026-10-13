import NLAlib.Polynomial.BestApproximation.GapJacobian
import NLAlib.ForMathlib.LinearAlgebra.Matrix.PeakDifference

/-!
# Positive normal and invertible differences of the actual peak Jacobian

The signed positive relation of divided derivatives gives a strictly positive normalized
left normal of the actual peak Jacobian. Every actual peak-difference derivative is invertible.
Source: focused rederivations, `polyretry:positive-normal`.
-/

noncomputable section

open Polynomial Matrix Finset

namespace NLAlib

/-- The actual interpolation peak Jacobian has a strictly positive normalized left nullvector.
Source: positive Laplacian cofactors and the alternating nodal-product sign.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem exists_pos_vecMul_interpolationGapJacobian_eq_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) :
    ∃ w : Fin (n + 1) → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      w ᵥ* interpolationGapJacobian n t = 0 := by
  obtain ⟨π, hπ, hπsum, hpoly⟩ := exists_pos_sum_smul_gapDirection_eq_zero hn ht
  let ω := fun i => (Lagrange.nodal univ (canonicalIntervalNodes n t)).eval (interpolationGapCriticalPoint n t i)
  let a := fun i => π i / |ω i|
  have hω : ∀ i, ω i ≠ 0 := eval_nodal_interpolationGapCriticalPoint_ne_zero hn ht
  have ha : ∀ i, 0 < a i := fun i => div_pos (hπ i) (abs_pos.mpr (hω i))
  have hmul : ∀ i, a i * ω i = (-1 : ℝ) ^ (n + 1) * ((-1 : ℝ) ^ i.val * π i) := by
    intro i
    have hsign := eval_nodal_gap_eq_sign_mul_abs ht i (interpolationGapCriticalPoint_spec hn ht i).1
    change ω i = (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ i.val * |ω i| at hsign
    dsimp [a]
    nth_rw 2 [hsign]
    have hden : |ω i| ≠ 0 := abs_ne_zero.mpr (hω i)
    field_simp
  have hker : a ᵥ* interpolationGapJacobian n t = 0 := by
    ext j
    have heval := congrArg (fun p : ℝ[X] => p.eval (t j)) hpoly
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, eval_zero] at heval
    change (∑ i, a i * interpolationGapJacobian n t i j) = 0
    have hterm : ∀ i, a i * interpolationGapJacobian n t i j =
        (Lagrange.nodalWeight univ (canonicalIntervalNodes n t) j.castSucc.succ * (-1 : ℝ) ^ (n + 1)) *
          (((-1 : ℝ) ^ i.val * π i) * (interpolationGapDividedDerivative n t i).eval (t j)) := by
      intro i
      dsimp [interpolationGapJacobian]
      change a i * (ω i * Lagrange.nodalWeight univ (canonicalIntervalNodes n t) j.castSucc.succ *
        (interpolationGapDividedDerivative n t i).eval (t j)) = _
      rw [← mul_assoc, ← mul_assoc, hmul]
      ring
    simp_rw [hterm]
    rw [← mul_sum, heval, mul_zero]
  have hasum : 0 < ∑ i, a i := sum_pos (fun i hi => ha i) univ_nonempty
  refine ⟨fun i => a i / ∑ k, a k, fun i => div_pos (ha i) hasum, ?_, ?_⟩
  · rw [← sum_div]
    exact div_self hasum.ne'
  · ext j
    change (∑ i, (a i / ∑ k, a k) * interpolationGapJacobian n t i j) = 0
    simp only [div_mul_eq_mul_div, ← sum_div]
    rw [show (∑ i, a i * interpolationGapJacobian n t i j) = 0 from congrFun hker j, zero_div]

/-- The actual peak-difference Jacobian has nonzero determinant.
Source: full actual Jacobian rank and its normalized positive left normal.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem det_interpolationGapJacobian_difference_ne_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) :
    Matrix.det (fun i j : Fin n => interpolationGapJacobian n t i.succ j - interpolationGapJacobian n t 0 j) ≠ 0 := by
  obtain ⟨w, hw, hsum, hker⟩ := exists_pos_vecMul_interpolationGapJacobian_eq_zero hn ht
  apply det_row_difference_ne_zero (interpolationGapJacobian n t) ?_ w hsum hker
  have hdet := det_interpolationGapJacobian_minor_ne_zero hn ht (0 : Fin (n + 1))
  have heq : (interpolationGapJacobian n t).submatrix (0 : Fin (n + 1)).succAbove id =
      (fun i j : Fin n => interpolationGapJacobian n t i.succ j) := by
    ext i j
    simp only [Matrix.submatrix_apply, Fin.succAbove_zero, id_eq]
  rw [heq] at hdet
  exact hdet

end NLAlib
