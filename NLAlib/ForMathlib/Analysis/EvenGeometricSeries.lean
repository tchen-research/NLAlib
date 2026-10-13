import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Ring.Parity

/-! # Even geometric series

A support-preserving reindexing of the even tail gives its sharp geometric estimate.
-/
noncomputable section
namespace NLAlib
/-- The even geometric tail beyond degree `n` is at most the geometric series
starting at `n+1` with ratio `q²`. Source: scalar estimate in ATAP Theorems 19.3–19.4. -/
theorem tsum_even_geometric_tail_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (∑' k : ℕ, if n < k ∧ Even k then q ^ k else 0) ≤ q ^ (n + 1) / (1 - q ^ 2) := by
  let m := 2 * (n / 2 + 1)
  let f := fun k : ℕ => if n < k ∧ Even k then q ^ k else 0
  have hm : n < m := by dsimp [m]; omega
  have hinj : Function.Injective (fun j : ℕ => 2 * j + m) := by intro i j h; dsimp only at h; omega
  have hsup : Function.support f ⊆ Set.range (fun j : ℕ => 2 * j + m) := by
    intro k hk
    have hcond : n < k ∧ Even k := by
      by_contra h
      change f k ≠ 0 at hk
      simp [f, h] at hk
    have hke := Nat.even_iff.mp hcond.2
    refine ⟨k / 2 - (n / 2 + 1), ?_⟩
    dsimp [m]
    omega
  have heq := hinj.tsum_eq hsup
  have hgeom : (∑' j : ℕ, f (2 * j + m)) = q ^ m / (1 - q ^ 2) := by
    have hfun : (fun j : ℕ => f (2 * j + m)) = fun j => q ^ m * (q ^ 2) ^ j := by
      funext j
      have heven : Even (2 * j + m) := by dsimp [m]; rw [Nat.even_iff]; omega
      dsimp [f]
      rw [if_pos ⟨by omega, heven⟩, pow_add, pow_mul, mul_comm]
    rw [hfun, tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg q) (by nlinarith)]
    rfl
  rw [← heq, hgeom]
  apply div_le_div_of_nonneg_right _ (by nlinarith : 0 ≤ 1 - q ^ 2)
  exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)

/-- A geometric bound on positive-index coefficients bounds the absolute even tail.
Source: scalar coefficient-tail estimate in ATAP Theorems 19.3–19.4. -/
theorem tsum_even_abs_tail_le_of_geometric {c : ℕ → ℝ}
    (hs : Summable (fun k => |c k|)) {q M : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hc : ∀ k, 0 < k → |c k| ≤ 2 * M * q ^ k) (n : ℕ) :
    (∑' k, if n < k ∧ Even k then |c k| else 0) ≤
      2 * M * q ^ (n + 1) / (1 - q ^ 2) := by
  have ht : Summable (fun k => if n < k ∧ Even k then |c k| else 0) :=
    hs.of_nonneg_of_le (by intro k; split_ifs <;> positivity) (by intro k; split_ifs <;> simp)
  have hgeom : Summable (fun k : ℕ => if n < k ∧ Even k then 2 * M * q ^ k else 0) :=
    ((summable_geometric_of_lt_one hq0.le hq1).mul_left (2 * M)).of_nonneg_of_le
      (by intro k; split_ifs <;> positivity) (by intro k; split_ifs; rfl; positivity)
  calc _ ≤ ∑' k, if n < k ∧ Even k then 2 * M * q ^ k else 0 :=
      ht.tsum_le_tsum (by intro k; split_ifs with h; exact hc k (by omega); rfl) hgeom
    _ = 2 * M * (∑' k : ℕ, if n < k ∧ Even k then q ^ k else 0) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      split_ifs <;> simp
    _ ≤ 2 * M * (q ^ (n + 1) / (1 - q ^ 2)) :=
      mul_le_mul_of_nonneg_left (tsum_even_geometric_tail_le hq0 hq1 n) (by positivity)
    _ = _ := by ring

end NLAlib
