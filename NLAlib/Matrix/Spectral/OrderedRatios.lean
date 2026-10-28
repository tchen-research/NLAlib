import NLAlib.Matrix.Subspaces.OrderedFrames

/-!
# Consecutive absolute eigenvalue ratios

The maximum includes zero for the empty list, so dimensions zero and one have
rate zero. Strict absolute ordering makes every proper leading eigenvalue
nonzero, while permitting the last eigenvalue to vanish.
-/

noncomputable section
open scoped NNReal
namespace NLAlib

/-- Maximum consecutive modulus ratio, with value zero in dimensions below two. -/
def maxAdjacentAbsRatio {n : ℕ} (d : Fin n → ℝ) : ℝ :=
  ↑(Finset.univ.sup fun i : Fin n =>
    (⟨if h : i.val + 1 < n then |d ⟨i.val+1, h⟩| / |d i| else 0,
      by split_ifs <;> positivity⟩ : ℝ≥0))

/-- The maximum consecutive ratio is nonnegative, including empty lists. -/
theorem maxAdjacentAbsRatio_nonneg {n : ℕ} (d : Fin n → ℝ) :
    0 ≤ maxAdjacentAbsRatio d := NNReal.coe_nonneg _

/-- Every actual consecutive ratio is bounded by the finite maximum. -/
theorem adjacentAbsRatio_le_max {n : ℕ} (d : Fin n → ℝ) (i : Fin n)
    (hi : i.val + 1 < n) :
    |d ⟨i.val+1, hi⟩| / |d i| ≤ maxAdjacentAbsRatio d := by
  have h := Finset.le_sup (f := fun i : Fin n =>
    (⟨if h : i.val + 1 < n then |d ⟨i.val+1, h⟩| / |d i| else 0,
      by split_ifs <;> positivity⟩ : ℝ≥0)) (Finset.mem_univ i)
  change (if h : i.val + 1 < n then |d ⟨i.val+1, h⟩| / |d i| else 0) ≤
    maxAdjacentAbsRatio d at h
  simpa only [dif_pos hi] using h

/-- Strictly decreasing absolute values give a geometric ratio below one, even
when the last value is zero.
atlas: qr-algorithm-convergence (partial) -/
theorem maxAdjacentAbsRatio_lt_one {n : ℕ} {d : Fin n → ℝ}
    (hd : StrictAnti fun i => |d i|) : maxAdjacentAbsRatio d < 1 := by
  unfold maxAdjacentAbsRatio
  apply NNReal.coe_lt_one.mpr
  apply (Finset.sup_lt_iff (α := NNReal) (a := 1) (by norm_num)).mpr
  intro i _
  change (if h : i.val + 1 < n then |d ⟨i.val+1, h⟩| / |d i| else 0) < (1 : ℝ)
  split_ifs with hi
  · have hlt := hd (show i < (⟨i.val+1, hi⟩ : Fin n) from Fin.lt_def.mpr (Nat.lt_succ_self _))
    exact (div_lt_one (lt_of_le_of_lt (abs_nonneg _) hlt)).mpr hlt
  · norm_num

end NLAlib
