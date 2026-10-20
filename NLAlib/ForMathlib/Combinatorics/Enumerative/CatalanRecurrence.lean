import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Uniqueness of the even-Catalan convolution sequence

The sequence with zeroth value one, first value zero and the native binary
convolution recursion has odd terms zero and even terms the Catalan numbers.
The result is purely algebraic and preserves the natural Catalan normalization.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical

private theorem sum_range_ite_even_div_two {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1), if Even k then f (k / 2) else 0) =
      ∑ j ∈ Finset.range (n + 1), f j := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => k / 2)
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).1
    simp only [Finset.mem_range] at hk' ⊢
    omega
  · intro k hk l hl hEq
    have hkEven := Nat.even_iff.mp (Finset.mem_filter.mp hk).2
    have hlEven := Nat.even_iff.mp (Finset.mem_filter.mp hl).2
    omega
  · intro j hj
    refine ⟨2 * j, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, Nat.even_iff.mpr ?_⟩ <;>
        have hj' := Finset.mem_range.mp hj <;> omega
    · omega
  · intro k _
    rfl

private theorem ite_even_catalan_succ_succ {R : Type*} [Semiring R] (n : ℕ) :
    (if Even (n + 2) then (catalan ((n + 2) / 2) : R) else 0) =
      ∑ k ∈ Finset.range (n + 1),
        (if Even k then (catalan (k / 2) : R) else 0) *
          (if Even (n - k) then (catalan ((n - k) / 2) : R) else 0) := by
  by_cases hn : Even n
  · obtain ⟨a, rfl⟩ := even_iff_exists_two_mul.mp hn
    have hEven : Even (2 * a + 2) := Nat.even_iff.mpr (by omega)
    have hDiv : (2 * a + 2) / 2 = a + 1 := by omega
    rw [if_pos hEven, hDiv]
    calc
      (catalan (a + 1) : R) =
          ∑ j ∈ Finset.range (a + 1), (catalan j : R) * (catalan (a - j) : R) := by
        simp only [catalan_succ, Nat.cast_sum, Nat.cast_mul, Finset.sum_range]
      _ = ∑ k ∈ Finset.range (2 * a + 1),
          if Even k then (catalan (k / 2) : R) * (catalan (a - k / 2) : R) else 0 :=
        (sum_range_ite_even_div_two (fun j => (catalan j : R) * (catalan (a - j) : R)) a).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkEven : Even k
        · have hk' := Finset.mem_range.mp hk
          have hkMod := Nat.even_iff.mp hkEven
          have hRest : Even (2 * a - k) := Nat.even_iff.mpr (by omega)
          have hRestDiv : (2 * a - k) / 2 = a - k / 2 := by omega
          simp only [if_pos hkEven, if_pos hRest, hRestDiv]
        · simp only [if_neg hkEven, zero_mul]
  · have hnMod : n % 2 ≠ 0 := fun h => hn (Nat.even_iff.mpr h)
    have hEven : ¬Even (n + 2) := by
      intro h
      have hMod := Nat.even_iff.mp h
      omega
    rw [if_neg hEven]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkEven : Even k
    · have hk' := Finset.mem_range.mp hk
      have hkMod := Nat.even_iff.mp hkEven
      have hRest : ¬Even (n - k) := by
        intro h
        have hMod := Nat.even_iff.mp h
        omega
      simp only [if_neg hRest, mul_zero]
    · simp only [if_neg hkEven, zero_mul]

/-- A sequence with initial values one and zero and the exact binary
convolution recursion is zero at odd indices and Catalan at even indices.
The coefficients may lie in any semiring. -/
theorem eq_ite_even_catalan_of_recursion {R : Type*} [Semiring R]
    (f : ℕ → R) (hZero : f 0 = 1) (hOne : f 1 = 0)
    (hStep : ∀ n, f (n + 2) = ∑ k ∈ Finset.range (n + 1), f k * f (n - k)) (n : ℕ) :
    f n = if Even n then (catalan (n / 2) : R) else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [hZero]
    | succ n =>
      cases n with
      | zero => simp [hOne]
      | succ n =>
        calc
          f (n + 2) = ∑ k ∈ Finset.range (n + 1), f k * f (n - k) := hStep n
          _ = ∑ k ∈ Finset.range (n + 1),
              (if Even k then (catalan (k / 2) : R) else 0) *
                (if Even (n - k) then (catalan ((n - k) / 2) : R) else 0) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' := Finset.mem_range.mp hk
            rw [ih k (by omega), ih (n - k) (by omega)]
          _ = _ := (ite_even_catalan_succ_succ n).symm
