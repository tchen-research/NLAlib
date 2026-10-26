import NLAlib.Matrix.Structured.ProfileMasks
import NLAlib.Matrix.Norms.FiniteBlockSupport

/-!
# Spectral norm of the explicit diagonal profile masks

The two diagonal masks are supported on disjoint blocks of their respective
parity. Their spectral norms are therefore bounded by the maximum of their
finitely many supporting block norms, with no loss depending on the number
of blocks. Source: Latała--van Handel--Youssef (2018), Section 3.2.
-/

noncomputable section

namespace NLAlib

/-- Restrict a matrix to one of the successive overlapping diagonal blocks. -/
def profileBlockPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if InProfileBlock t i.val ∧ InProfileBlock t j.val then A i j else 0

private theorem unique_profile_block {n color : ℕ} (i : Fin n)
    (k l : {t : Fin (n + 1) // t.val % 2 = color})
    (hk : InProfileBlock k.val i.val) (hl : InProfileBlock l.val i.val) : k = l := by
  apply Subtype.ext
  apply Fin.ext
  by_contra hne
  exact not_inProfileBlock_of_same_parity hne (k.property.trans l.property.symm) hk hl

/-- The even-block profile part is bounded by any common bound on its
supporting blocks. The initial block and empty dimensions are included. -/
theorem specNorm_profileFirstPart_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ t ≤ n, t % 2 = 0 → specNorm (profileBlockPart A t) ≤ c) :
    specNorm (profileFirstPart A) ≤ c := by
  classical
  let T := {t : Fin (n + 1) // t.val % 2 = 0}
  refine specNorm_le_of_disjoint_block_bounds (profileFirstPart A)
    (fun t : T => fun i => InProfileBlock t.val i.val)
    (fun i k l => unique_profile_block i k l) ?_
    (fun t => profileBlockPart A t.val) ?_ hc ?_
  · intro i j hij
    have hm : ProfileFirstMask i.val j.val := by
      by_contra hn
      exact hij (by simp [profileFirstPart, hn])
    obtain ⟨t, ht, hi, hj⟩ := (profileFirstMask_iff_exists_fin i j).mp hm
    exact ⟨⟨t, ht⟩, hi, hj⟩
  · intro t i j hi hj
    have hm : ProfileFirstMask i.val j.val := ⟨t.val, t.property, hi, hj⟩
    simp [profileFirstPart, profileBlockPart, hm, hi, hj]
  · intro t
    exact hB t.val (Nat.le_of_lt_succ t.val.isLt) t.property

/-- The odd-block profile part is bounded by any common bound on its
supporting blocks after removal of its overlap with the first part. -/
theorem specNorm_profileSecondPart_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ t ≤ n, t % 2 = 1 →
      specNorm (profileBlockPart (profileSecondPart A) t) ≤ c) :
    specNorm (profileSecondPart A) ≤ c := by
  classical
  let T := {t : Fin (n + 1) // t.val % 2 = 1}
  refine specNorm_le_of_disjoint_block_bounds (profileSecondPart A)
    (fun t : T => fun i => InProfileBlock t.val i.val)
    (fun i k l => unique_profile_block i k l) ?_
    (fun t => profileBlockPart (profileSecondPart A) t.val) ?_ hc ?_
  · intro i j hij
    have hm : ProfileSecondMask i.val j.val := by
      by_contra hn
      exact hij (by simp [profileSecondPart, hn])
    obtain ⟨t, ht, hi, hj⟩ := (profileOddBlockMask_iff_exists_fin i j).mp hm.1
    exact ⟨⟨t, ht⟩, hi, hj⟩
  · intro t i j hi hj
    simp [profileBlockPart, hi, hj]
  · intro t
    exact hB t.val (Nat.le_of_lt_succ t.val.isLt) t.property

end NLAlib
