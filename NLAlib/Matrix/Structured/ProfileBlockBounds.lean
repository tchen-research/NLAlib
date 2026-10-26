import NLAlib.Matrix.Structured.ProfileBlockNorms
import NLAlib.ForMathlib.Analysis.FiniteHeavySets

/-!
# Energy and support bounds for the explicit profile blocks

Masking retains symmetry and decreases every squared entry. The supporting
coordinate count of a block is bounded by its neighbor cutoff.
-/

noncomputable section
namespace NLAlib

/-- The finite coordinate support of a diagonal profile block. -/
def profileBlockCoordinates (n t : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => InProfileBlock t i.val

/-- The number of coordinates in a block is at most its upper cutoff. -/
theorem card_profileBlockCoordinates_le (n t : ℕ) :
    (profileBlockCoordinates n t).card ≤ profileNeighborCutoff t := by
  classical
  apply Finset.card_filter_le_of_imp_val_lt
  exact fun _ h => h.2

/-- Every squared entry of a diagonal block is bounded by the original squared
entry, with no sign assumption. -/
theorem profileBlockPart_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ) (i j : Fin n) : profileBlockPart A t i j ^ 2 ≤ A i j ^ 2 := by
  classical
  unfold profileBlockPart
  split_ifs <;> simp [sq_nonneg]

/-- All three profile masks decrease squared entries. -/
theorem profile_parts_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    profileFirstPart A i j ^ 2 ≤ A i j ^ 2 ∧
      profileSecondPart A i j ^ 2 ≤ A i j ^ 2 ∧
      profileRemainderPart A i j ^ 2 ≤ A i j ^ 2 := by
  classical
  constructor
  · unfold profileFirstPart; split_ifs <;> simp [sq_nonneg]
  constructor
  · unfold profileSecondPart; split_ifs <;> simp [sq_nonneg]
  · unfold profileRemainderPart; split_ifs <;> simp [sq_nonneg]

/-- A diagonal block of a symmetric matrix is symmetric. -/
theorem isSymm_profileBlockPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (t : ℕ) : (profileBlockPart A t).IsSymm := by
  classical
  ext i j
  simp only [Matrix.transpose_apply, profileBlockPart, hA.apply i j, and_comm]

/-- A profile block vanishes in every row outside its coordinate support. -/
theorem profileBlockPart_eq_zero_of_not_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ) (i : Fin n) (hi : i ∉ profileBlockCoordinates n t) (j : Fin n) :
    profileBlockPart A t i j = 0 := by
  classical
  have hn : ¬ InProfileBlock t i.val := by simpa [profileBlockCoordinates] using hi
  simp [profileBlockPart, hn]

/-- Row square-energy does not increase when restricting to a profile block. -/
theorem sum_row_sq_profileBlockPart_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ) (i : Fin n) :
    (∑ j, profileBlockPart A t i j ^ 2) ≤ ∑ j, A i j ^ 2 :=
  Finset.sum_le_sum fun j _ => profileBlockPart_sq_le A t i j

end NLAlib
