import NLAlib.Matrix.Structured.JacobiBorderPowers
import NLAlib.Matrix.Structured.LastResolvent
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # The monic characteristic polynomial of the actual last border

The scalar Schur determinant and last-coordinate resolvent cofactor prove the
appended-border characteristic recurrence. Extending the identity across the finite
old spectrum uses polynomial equality on an infinite set, with no division at a root.
-/

noncomputable section
open Matrix Polynomial Finset
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual scalar border determinant is its leading determinant times the
scalar Schur complement whenever the leading block is invertible. -/
theorem det_symmetricBorder_eq_det_mul_schur (J : Matrix n n ℝ) (v : n → ℝ) (d : ℝ)
    (hJ : IsUnit J) : (symmetricBorder J v d).det = J.det * (d - quadForm J⁻¹ v) := by
  let : Invertible J := hJ.invertible
  rw [symmetricBorder, Matrix.det_fromBlocks₁₁, invOf_eq_nonsing_inv, schur_symmetricBorder]
  rw [Matrix.det_eq_elem_of_subsingleton _ (0 : Fin 1)]
  rfl

/-- A single-coordinate quadratic form equals its squared amplitude times the
corresponding diagonal matrix entry. -/
theorem quadForm_single (A : Matrix n n ℝ) (i : n) (c : ℝ) :
    quadForm A (Pi.single i c) = c ^ 2 * A i i := by
  simp [quadForm, dotProduct, Matrix.mulVec, Pi.single_apply]
  ring

variable {q : ℕ}

/-- The actual symmetric last-coordinate border has the classical monic
characteristic-polynomial recurrence. No tridiagonal shape is needed; the off-spectrum
Schur calculation is extended to a polynomial identity at every point.
Source: focused mathematical reroutes, Section 3 (BL6), after (BL10).
atlas: gauss-radau-lobatto (partial) -/
theorem charpoly_symmetricBorder_single_last
    (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (b d : ℝ) :
    (symmetricBorder J (Pi.single (Fin.last q) b) d).charpoly =
      (X - C d) * J.charpoly - C (b ^ 2) * (J.submatrix Fin.castSucc Fin.castSucc).charpoly := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Polynomial.finite_setOfPred_isRoot J.charpoly_monic.ne_zero).infinite_compl.mono
  intro z hz
  have hz' : J.charpoly.eval z ≠ 0 := hz
  have hJ : IsUnit (z • 1 - J) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    simpa only [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.diagonal_one,
      ← Matrix.diagonal_smul, Pi.smul_def, smul_eq_mul, mul_one] using hz'
  have hshift : Matrix.scalar _ z - symmetricBorder J (Pi.single (Fin.last q) b) d =
      symmetricBorder (z • 1 - J) (-(Pi.single (Fin.last q) b)) (z - d) := by
    have hs : Matrix.scalar (Fin (q + 1) ⊕ Fin 1) z = z • 1 := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    rw [hs, smul_one_sub_symmetricBorder]
  simp only [Set.mem_ofPred_eq, eval_sub, eval_mul, eval_X, eval_C]
  rw [Matrix.eval_charpoly, hshift, det_symmetricBorder_eq_det_mul_schur _ _ _ hJ]
  have hneg : (-(Pi.single (Fin.last q) b) : Fin (q + 1) → ℝ) = Pi.single (Fin.last q) (-b) := by
    ext i
    by_cases hi : i = Fin.last q <;> simp [hi]
  rw [hneg, quadForm_single, neg_sq, resolvent_last_last_eq_charpoly_leading_div_charpoly]
  have hdet : (z • 1 - J).det = J.charpoly.eval z := by
    rw [Matrix.eval_charpoly, Matrix.scalar_apply]
    congr 1
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  rw [hdet]
  field_simp

end NLAlib
