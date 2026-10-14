import NLAlib.Matrix.Structured.Hessenberg
import Mathlib.Tactic

/-! # Finite propagation and rooted moment locality

Hessenberg powers propagate at most one coordinate per multiplication. The finite
noncommutative telescope then proves that distant tridiagonal perturbations preserve
the first-coordinate moments to their exact degree thresholds.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace NLAlib

/-- The finite matrix-power telescope, valid without commuting the two ring elements.
Source: focused mathematical reroutes, Section 3, equation (BL1). -/
theorem pow_sub_pow_eq_sum_mul_sub_mul {R : Type*} [Ring R] (A B : R) (k : ℕ) :
    A ^ k - B ^ k = ∑ r ∈ range k, A ^ r * (A - B) * B ^ (k - 1 - r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmul : (A ^ k - B ^ k) * B =
        ∑ r ∈ range k, A ^ r * (A - B) * B ^ (k - r) := by
      rw [ih, sum_mul]
      apply sum_congr rfl
      intro r hr
      rw [mul_assoc, ← pow_succ, show k - 1 - r + 1 = k - r by
        have := mem_range.mp hr; omega]
    rw [sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    rw [← hmul, pow_succ, pow_succ]
    noncomm_ring

variable {n : ℕ}

/-- An upper-Hessenberg transpose propagates its first row by at most one index at
each power. The dimension-one and zeroth-power cases are included. -/
theorem IsUpperHessenberg.pow_apply_zero_left_eq_zero
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUpperHessenberg Aᵀ) (hn : 0 < n)
    (r : ℕ) (i : Fin n) (hi : r < i.val) : (A ^ r) ⟨0, hn⟩ i = 0 := by
  induction r generalizing i with
  | zero =>
    have hne : (⟨0, hn⟩ : Fin n) ≠ i := by intro h; have := congrArg Fin.val h; simp at this; omega
    simp [hne]
  | succ r ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply sum_eq_zero
    intro j _
    by_cases hj : r < j.val
    · rw [ih j hj, zero_mul]
    · rw [show A j i = 0 from hA i j (by omega), mul_zero]

/-- An upper Hessenberg matrix propagates its first column by at most one index at
each power. -/
theorem IsUpperHessenberg.pow_apply_zero_right_eq_zero
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUpperHessenberg A) (hn : 0 < n)
    (r : ℕ) (i : Fin n) (hi : r < i.val) : (A ^ r) i ⟨0, hn⟩ = 0 := by
  have h := IsUpperHessenberg.pow_apply_zero_left_eq_zero
    (A := Aᵀ) (by simpa only [transpose_transpose] using hA) hn r i hi
  rw [← transpose_pow] at h
  exact h

/-- Two tridiagonal matrices agreeing below the anti-diagonal `i+j=s` have equal
first-coordinate moments through degree `s`. No symmetry or irreducibility is used.
Source: focused mathematical reroutes, Section 3, equation (BL1).
atlas: gauss-radau-lobatto (partial) -/
theorem pow_apply_zero_eq_of_isTridiagonal_of_eq_below_add
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : IsTridiagonal A) (hB : IsTridiagonal B)
    (hn : 0 < n) (s : ℕ) (hAB : ∀ i j : Fin n, i.val + j.val < s → A i j = B i j)
    (k : ℕ) (hk : k ≤ s) : (A ^ k) ⟨0, hn⟩ ⟨0, hn⟩ = (B ^ k) ⟨0, hn⟩ ⟨0, hn⟩ := by
  apply sub_eq_zero.mp
  change (A ^ k - B ^ k) ⟨0, hn⟩ ⟨0, hn⟩ = 0
  rw [pow_sub_pow_eq_sum_mul_sub_mul]
  simp only [Matrix.sum_apply]
  apply sum_eq_zero
  intro r hr
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro j _
  rw [Matrix.mul_apply]
  rw [sum_mul]
  apply sum_eq_zero
  intro i _
  by_cases hi : r < i.val
  · rw [hA.2.pow_apply_zero_left_eq_zero hn r i hi, zero_mul, zero_mul]
  by_cases hj : k - 1 - r < j.val
  · rw [hB.1.pow_apply_zero_right_eq_zero hn (k - 1 - r) j hj, mul_zero]
  have hij : i.val + j.val < s := by have := mem_range.mp hr; omega
  rw [show (A - B) i j = 0 by simp only [Matrix.sub_apply, hAB i j hij, sub_self],
    mul_zero, zero_mul]

end NLAlib
