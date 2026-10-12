import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Upper quasitriangular matrices

Only the first subdiagonal may be nonzero, and its nonzero entries are
nonadjacent. These are exactly the zero conditions for upper block triangular
matrices with consecutive diagonal blocks of sizes one and two.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Upper quasitriangular means zeros below the first subdiagonal and no
two adjacent nonzero subdiagonal entries, giving consecutive diagonal blocks
of size at most two. Source: Horn–Johnson (2013), §2.3 and Theorem 2.6.2.
The predicate records the block zero pattern; any spectral restrictions on
the two-dimensional blocks are stated separately. -/
def IsUpperQuasiTriangular {k : ℕ} {K : Type*} [Zero K]
    (T : Matrix (Fin k) (Fin k) K) : Prop :=
  (∀ i j, j.val + 1 < i.val → T i j = 0) ∧
  (∀ i j l, j.val + 1 = i.val → l.val + 1 = j.val → T i j = 0 ∨ T j l = 0)

/-- Every upper triangular matrix is upper quasitriangular. Source:
Horn–Johnson (2013), §2.3; all diagonal blocks may be taken scalar. -/
theorem isUpperQuasiTriangular_of_isUpperTriangular
    {k : ℕ} {K : Type*} [Zero K] {T : Matrix (Fin k) (Fin k) K}
    (hT : T.IsUpperTriangular) : IsUpperQuasiTriangular T := by
  constructor
  · intro i j hij
    exact hT (show j < i by omega)
  · intro i j l hij _
    exact Or.inl (hT (show j < i by omega))

/-- In a product of an upper triangular and upper quasitriangular matrix,
each first-subdiagonal entry is scaled only by the corresponding diagonal
entry of the left factor. Source: block multiplication; real QZ helper. -/
theorem mul_apply_subdiagonal_of_upperTriangular
    {k : ℕ} {K : Type*} [Semiring K] {R T : Matrix (Fin k) (Fin k) K}
    (hR : R.IsUpperTriangular) (hT : IsUpperQuasiTriangular T)
    {i j : Fin k} (hij : j.val + 1 = i.val) : (R * T) i j = R i i * T i j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro l _ hli
    by_cases hlt : l < i
    · rw [hR hlt, zero_mul]
    · rw [hT.1 l j (by have := Fin.val_ne_of_ne hli; omega), mul_zero]
  · simp

/-- Left multiplication by an upper triangular matrix preserves upper
quasitriangularity and its block boundaries. Source: Horn–Johnson (2013),
Theorem 2.6.2; this is the final real QR step for the second pencil factor. -/
theorem IsUpperQuasiTriangular.upperTriangular_mul
    {k : ℕ} {K : Type*} [Semiring K] {R T : Matrix (Fin k) (Fin k) K}
    (hT : IsUpperQuasiTriangular T) (hR : R.IsUpperTriangular) :
    IsUpperQuasiTriangular (R * T) := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hlt : l < i
    · rw [hR hlt, zero_mul]
    · rw [hT.1 l j (by omega), mul_zero]
  · intro i j l hij hjl
    rw [mul_apply_subdiagonal_of_upperTriangular hR hT hij,
      mul_apply_subdiagonal_of_upperTriangular hR hT hjl]
    rcases hT.2 i j l hij hjl with h | h
    · exact Or.inl (by rw [h, mul_zero])
    · exact Or.inr (by rw [h, mul_zero])

/-- Prefixing one scalar block to an upper quasitriangular trailing matrix
preserves quasitriangularity. Source: Horn–Johnson (2013), Theorem 2.6.2;
the first row is unrestricted and the lower first column is zero. -/
theorem isUpperQuasiTriangular_of_first_column_and_tail
    {k : ℕ} {K : Type*} [Zero K] {T : Matrix (Fin (k + 1)) (Fin (k + 1)) K}
    (hcol : ∀ i : Fin k, T i.succ 0 = 0)
    (htail : IsUpperQuasiTriangular (T.submatrix Fin.succ Fin.succ)) :
    IsUpperQuasiTriangular T := by
  constructor
  · intro i j hij
    revert hij
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij
      have hi : i ≠ 0 := by intro h; simp [h] at hij
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
      exact hcol i
    · refine Fin.cases ?_ (fun i => ?_) i
      · intro h; simp at h
      · intro h
        exact htail.1 i j (by simpa using h)
  · intro i j l hij hjl
    have hi : i ≠ 0 := by intro h; simp [h] at hij
    have hj : j ≠ 0 := by intro h; simp [h] at hjl
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
    revert hjl
    refine Fin.cases ?_ (fun l => ?_) l
    · intro _; exact Or.inr (hcol j)
    · intro hjl
      exact htail.2 i j l (by simpa using hij) (by simpa using hjl)

end NLAlib
