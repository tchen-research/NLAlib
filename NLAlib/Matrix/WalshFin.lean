import NLAlib.Matrix.Walsh
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The actual normalized Walsh transform on ordinary finite labels

The binary character construction is relabeled to `Fin (2^b)` so it applies
directly to the classical SRHT law. Source: `sh:srht`, atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical Matrix
namespace NLAlib

/-- A fixed relabeling of the binary Walsh group by ordinary row labels.
Source: the genuine binary character construction, `sh:srht`. -/
def walshIndexEquivFin (b : ℕ) : WalshIndex b ≃ Fin (2 ^ b) :=
  Fintype.equivOfCardEq (by simp only [card_walshIndex, Fintype.card_fin])

/-- The actual normalized Walsh matrix, now on ordinary finite row labels.
Source: operator re-derivation `sh:srht`. -/
def walshMatrixFin (b : ℕ) : Matrix (Fin (2 ^ b)) (Fin (2 ^ b)) ℝ :=
  fun i j => walshMatrix b ((walshIndexEquivFin b).symm i) ((walshIndexEquivFin b).symm j)

/-- The actual finite-label Walsh transform is orthogonal.
Source: binary character orthogonality, `sh:srht`. -/
theorem walshMatrixFin_transpose_mul_self (b : ℕ) :
    (walshMatrixFin b)ᵀ * walshMatrixFin b = 1 := by
  ext a c
  let e := walshIndexEquivFin b
  have hh := congrArg (fun M : Matrix (WalshIndex b) (WalshIndex b) ℝ =>
    M (e.symm a) (e.symm c)) (walshMatrix_transpose_mul_self b)
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hh ⊢
  change (∑ j : Fin (2 ^ b), walshMatrix b (e.symm j) (e.symm a) *
    walshMatrix b (e.symm j) (e.symm c)) = _
  calc
    _ = ∑ j : WalshIndex b, walshMatrix b j (e.symm a) * walshMatrix b j (e.symm c) :=
      e.symm.sum_comp (fun j => walshMatrix b j (e.symm a) * walshMatrix b j (e.symm c))
    _ = (1 : Matrix (WalshIndex b) (WalshIndex b) ℝ) (e.symm a) (e.symm c) := hh
    _ = _ := by simp only [Matrix.one_apply, e.symm.injective.eq_iff]

/-- Every actual finite-label Walsh entry is flat.
Source: normalized binary characters, `sh:srht`. -/
theorem walshMatrixFin_apply_sq (b : ℕ) (i j : Fin (2 ^ b)) :
    walshMatrixFin b i j ^ 2 = 1 / ((2 ^ b : ℕ) : ℝ) := by
  simpa only [walshMatrixFin, Nat.cast_pow, Nat.cast_ofNat] using
    walshMatrix_apply_sq b ((walshIndexEquivFin b).symm i) ((walshIndexEquivFin b).symm j)

end NLAlib
