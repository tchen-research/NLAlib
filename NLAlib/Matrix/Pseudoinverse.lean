import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Pseudoinverses

Full-rank special cases of the Moore–Penrose pseudoinverse, as the sources use them:

* `NLAlib.pinvL G = (Gᵀ G)⁻¹ Gᵀ`, equal to `G†` when `G` has full column rank;
* `NLAlib.pinvR G = Gᵀ (G Gᵀ)⁻¹`, equal to `G†` when `G` has full row rank.

Mathlib's `⁻¹` on matrices is total (it returns `0` on singular input), so these are honest
definitions; the only property most arguments use is the one-sided inverse identity, which
holds under the corresponding `IsUnit` hypothesis. The general Moore–Penrose definition with
the four Penrose identities is atlas target `pseudoinverse`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Left pseudoinverse `(Gᵀ G)⁻¹ Gᵀ`. -/
def pinvL [DecidableEq n] (G : Matrix m n ℝ) : Matrix n m ℝ := (Gᵀ * G)⁻¹ * Gᵀ

/-- Right pseudoinverse `Gᵀ (G Gᵀ)⁻¹`. -/
def pinvR [DecidableEq m] (G : Matrix m n ℝ) : Matrix n m ℝ := Gᵀ * (G * Gᵀ)⁻¹

theorem pinvL_mul [DecidableEq n] {G : Matrix m n ℝ} (h : IsUnit (Gᵀ * G)) :
    pinvL G * G = 1 := by
  unfold pinvL
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h)]

theorem mul_pinvR [DecidableEq m] {G : Matrix m n ℝ} (h : IsUnit (G * Gᵀ)) :
    G * pinvR G = 1 := by
  unfold pinvR
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h)]

end NLAlib
