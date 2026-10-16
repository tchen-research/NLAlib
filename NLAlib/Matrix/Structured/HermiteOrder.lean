import NLAlib.Matrix.Structured.HermiteLadders
import Mathlib.Analysis.Matrix.Order

/-! # Order of the finite Hermite interior projection

The number matrix is bounded by `p - 1` after restricting to the interior
cutoff. This explicitly avoids using the false unrestricted commutator at
the top degree. Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

/-- The finite occupation interior projector is Hermitian. -/
theorem isHermitian_hermiteInterior : (hermiteInterior (ι := ι) p).IsHermitian := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [hermiteInterior, Matrix.diagonal_apply, apply_ite]
  · simp [hermiteInterior, Matrix.diagonal_apply, hab, Ne.symm hab]

/-- The finite occupation interior projector is idempotent. -/
theorem hermiteInterior_mul_self :
    hermiteInterior (ι := ι) p * hermiteInterior p = hermiteInterior p := by
  rw [hermiteInterior, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases ha : a.degree < p <;> simp [ha]

/-- The finite occupation interior projector is PSD. -/
theorem posSemidef_hermiteInterior : (hermiteInterior (ι := ι) p).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro a
  dsimp
  split_ifs <;> positivity

/-- The finite occupation interior projector lies below the identity. -/
theorem hermiteInterior_le_one :
    hermiteInterior (ι := ι) p ≤ (1 : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ) := by
  apply Matrix.le_iff.mpr
  have he : 1 - hermiteInterior (ι := ι) p =
      diagonal (fun a : HermiteIndex ι p => if a.degree < p then (0 : ℂ) else 1) := by
    ext a b
    by_cases hab : a = b
    · subst b
      by_cases ha : a.degree < p <;> simp [hermiteInterior, Matrix.diagonal_apply, ha]
    · simp [hermiteInterior, Matrix.diagonal_apply, Matrix.one_apply, hab]
  rw [he]
  exact Matrix.PosSemidef.diagonal (fun a => by dsimp; split_ifs <;> positivity)

/-- The occupation number is at most `p - 1` on the interior cutoff. This
holds also at cutoff zero, where the interior projection vanishes. -/
theorem hermiteInterior_number_le :
    hermiteInterior (ι := ι) p * hermiteNumber p * hermiteInterior p ≤
      ((p - 1 : ℕ) : ℝ) • hermiteInterior p := by
  apply Matrix.le_iff.mpr
  have he : ((p - 1 : ℕ) : ℝ) • hermiteInterior (ι := ι) p -
      hermiteInterior p * hermiteNumber p * hermiteInterior p =
      diagonal (fun a : HermiteIndex ι p => if a.degree < p then
        ((((p - 1 : ℕ) : ℝ) - a.degree : ℝ) : ℂ) else 0) := by
    ext a b
    by_cases hab : a = b
    · subst b
      by_cases ha : a.degree < p
      · simp [hermiteInterior, hermiteNumber, Matrix.mul_diagonal, Matrix.diagonal_mul,
          Matrix.diagonal_apply, ha, Complex.ofReal_sub, Algebra.smul_def,
          Matrix.natCast_apply]
      · simp [hermiteInterior, hermiteNumber, Matrix.mul_diagonal, Matrix.diagonal_mul,
          Matrix.diagonal_apply, ha]
    · simp [hermiteInterior, hermiteNumber, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.diagonal_apply, hab]
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro a
  dsimp
  split_ifs with ha
  · exact_mod_cast (sub_nonneg.mpr
      (by exact_mod_cast (show a.degree ≤ p - 1 by omega)) :
      (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) - a.degree)
  · exact le_rfl

end NLAlib
