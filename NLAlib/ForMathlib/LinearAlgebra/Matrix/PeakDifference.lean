import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Invertibility of differences of peak rows

A rectangular Jacobian with full column rank and a normalized left normal has an invertible
matrix of row differences. Source: focused polynomial-approximation rederivations,
`polyretry:peak-jacobian`.
-/

noncomputable section

open Matrix Finset

namespace NLAlib

/-- The row-difference matrix of a full-rank rectangular Jacobian is invertible when the
left kernel contains a vector whose coordinates sum to one.
Source: focused rederivations, the peak-difference derivative. -/
theorem det_row_difference_ne_zero {n : ℕ}
    (J : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (hminor : Matrix.det (fun i j : Fin n => J i.succ j) ≠ 0)
    (w : Fin (n + 1) → ℝ) (hwsum : ∑ i, w i = 1) (hwJ : w ᵥ* J = 0) :
    Matrix.det (fun i j : Fin n => J i.succ j - J 0 j) ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hDv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let u := J *ᵥ v
  have hsucc : ∀ i : Fin n, u i.succ = u 0 := by
    intro i
    have h := congrFun hDv i
    change (∑ j, (J i.succ j - J 0 j) * v j) = 0 at h
    simp only [sub_mul, sum_sub_distrib] at h
    exact sub_eq_zero.mp h
  have hu : ∀ i : Fin (n + 1), u i = u 0 := by
    intro i
    exact Fin.cases rfl hsucc i
  have hwu : w ⬝ᵥ u = 0 := by
    dsimp [u]
    rw [dotProduct_mulVec, hwJ]
    simp [dotProduct]
  have hu0 : u 0 = 0 := by
    dsimp [dotProduct] at hwu
    simp_rw [hu] at hwu
    rw [← sum_mul, hwsum, one_mul] at hwu
    exact hwu
  have hJv : (fun i j : Fin n => J i.succ j) *ᵥ v = 0 := by
    ext i
    change u i.succ = 0
    rw [hsucc, hu0]
  exact hv (Matrix.eq_zero_of_mulVec_eq_zero hminor hJv)

end NLAlib
