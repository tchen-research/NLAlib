import NLAlib.Matrix.Basic.MoorePenrose
/-!
# Rank of the Moore–Penrose range projector

This deterministic fact is shared by perturbation and leverage-score proofs.
Source: Horn–Johnson 2013, Problem 7.3.P7; supports `pseudoinverse` and `leverage-scores`.
-/

noncomputable section
namespace NLAlib

/-- The rank of the Moore–Penrose column-space projector equals the original
matrix rank, including zero and empty shapes. Horn–Johnson 2013, Problem 7.3.P7. -/
theorem rank_mul_moorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : (A * moorePenroseInverse A).rank = A.rank := by
  refine le_antisymm (Matrix.rank_mul_le_left _ _) ?_
  calc A.rank = (A * moorePenroseInverse A * A).rank := by rw [mul_moorePenroseInverse_mul]
    _ ≤ (A * moorePenroseInverse A).rank := Matrix.rank_mul_le_left _ _

end NLAlib
