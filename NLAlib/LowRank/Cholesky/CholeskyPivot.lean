import NLAlib.LowRank.Nystrom.Structural
import NLAlib.Matrix.Basic.SingletonInverse
import NLAlib.Matrix.Basic.GramVanishing
import NLAlib.Matrix.Factorizations.CholeskyPivotProbability

/-!
# Coordinate Cholesky residual pivots

A single coordinate pivot `eliminationStep` (Matrix/Factorizations/EliminationStep) is the one-column
Nyström projResidual (`eliminationStep_eq_sub_nystrom`), also at zero pivots. The diagonal-over-trace
pivot probabilities `choleskyPivotProbability` give the one-step means of RPCholesky.
Source: Chen--Epperly--Tropp--Webber (2025); manuscript `sa:rp-update`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Cholesky coordinate pivot is the one-column Nyström residual:
`eliminationStep R i = R − nystrom R eᵢ`, including at a zero pivot (both sides are then `R`).
Source: manuscript `sa:rp-update`; CETW (2025), RPCholesky update. -/
theorem eliminationStep_eq_sub_nystrom (R : Matrix n n ℝ) (i : n) :
    eliminationStep R i = R - nystrom R (fun (j : n) (_ : Fin 1) => if j = i then 1 else 0) := by
  let E : Matrix n (Fin 1) ℝ := fun j _ => if j = i then 1 else 0
  have hcore : Eᵀ * R * E = Matrix.diagonal (fun _ : Fin 1 => R i i) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
    dsimp only [E]
    simp [ite_mul, mul_ite, Subsingleton.elim a b]
  ext j k
  rw [eliminationStep_apply]
  change _ = R j k - nystrom R E j k
  rw [nystrom, hcore, moorePenroseInverse_singleton]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one, Matrix.diagonal_apply]
  dsimp only [E]
  simp [ite_mul, mul_ite]
  ring

end NLAlib
