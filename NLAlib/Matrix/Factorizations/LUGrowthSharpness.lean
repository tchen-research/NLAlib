import NLAlib.Matrix.Factorizations.LU
/-!
# Sharpness of growth in Gaussian elimination with partial pivoting

The Wilkinson matrix has initial maximum entry one and the actual library
partial-pivoting recursion (including its first-index tie rule) produces
the final entry `2^n` in dimension `n+1`.

Source: Trefethen–Bau, Lecture 22; Golub–Van Loan, §3.4.6.
Atlas: `lu-growth-factor`.
-/
noncomputable section
open Matrix
namespace NLAlib

/-- Wilkinson's matrix, with a variable final column. The standard example
uses `t=1`; the parameter records the successive doubling during elimination. -/
def wilkinsonMatrix (n : ℕ) (t : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if (j : ℕ) = n then t else if i = j then 1 else if j < i then -1 else 0

/-- The first-index pivot rule selects the first entry whenever it has
largest modulus, including ties. -/
theorem absArgmax_eq_zero_of_forall {n : ℕ} (v : Fin (n + 1) → ℝ)
    (h : ∀ i, |v i| ≤ |v 0|) : absArgmax v = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp only [absArgmax, if_pos (h _)]

private theorem wilkinsonMatrix_first (n : ℕ) (t : ℝ) (i : Fin (n + 2)) :
    wilkinsonMatrix (n + 1) t i 0 = if i = 0 then 1 else -1 := by
  simp only [wilkinsonMatrix, Fin.val_zero, if_neg (by omega : ¬ (0 : ℕ) = n + 1)]
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi, Fin.pos_iff_ne_zero.mpr hi]

private theorem partialPivotSwap_wilkinsonMatrix (n : ℕ) (t : ℝ) :
    partialPivotSwap (wilkinsonMatrix (n + 1) t) = wilkinsonMatrix (n + 1) t := by
  have hp : absArgmax (fun i => wilkinsonMatrix (n + 1) t i 0) = 0 := by
    apply absArgmax_eq_zero_of_forall
    intro i
    simp only [wilkinsonMatrix_first]
    split_ifs <;> norm_num
  simp [partialPivotSwap, hp]

private theorem pivotSchur_wilkinsonMatrix (n : ℕ) (t : ℝ) :
    pivotSchur (wilkinsonMatrix (n + 1) t) = wilkinsonMatrix n (2 * t) := by
  ext i j
  have h0 : wilkinsonMatrix (n + 1) t 0 0 = 1 := by
    simp [wilkinsonMatrix_first]
  have hc : wilkinsonMatrix (n + 1) t i.succ 0 = -1 := by
    simp [wilkinsonMatrix_first]
  simp only [pivotSchur, h0, hc, inv_one, one_mul, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Matrix.submatrix_apply]
  simp only [wilkinsonMatrix, Fin.val_succ, Fin.succ_inj, Fin.succ_lt_succ_iff,
    Nat.add_right_cancel_iff]
  by_cases hj : (j : ℕ) = n
  · simp [hj]
    ring
  · have hj0 : ¬ (0 : Fin (n + 2)) = j.succ := Fin.succ_ne_zero j |>.symm
    simp [hj, hj0, show ¬ j.succ < (0 : Fin (n + 2)) from not_lt_of_ge (Fin.zero_le _)]

/-- The actual partial-pivoting recursion attains Wilkinson's exponential
growth, with its implemented tie rule. The last pivot in dimension `n+1`
is `2^n t`. Trefethen–Bau, Lecture 22.
atlas: lu-growth-factor (partial) -/
theorem luPartialPivot_wilkinsonMatrix_last (n : ℕ) (t : ℝ) :
    (luPartialPivot (wilkinsonMatrix n t)).2.2 (Fin.last n) (Fin.last n) = 2 ^ n * t := by
  induction n generalizing t with
  | zero => simp [luPartialPivot, partialPivotSwap, absArgmax, wilkinsonMatrix, borderedMatrix]
  | succ n ih =>
    simp only [luPartialPivot, partialPivotSwap_wilkinsonMatrix, pivotSchur_wilkinsonMatrix]
    change (luPartialPivot (wilkinsonMatrix n (2 * t))).2.2 (Fin.last n) (Fin.last n) = _
    rw [ih, pow_succ]
    ring

/-- Every entry of the initial Wilkinson matrix has magnitude at most one. -/
theorem abs_wilkinsonMatrix_one_le (n : ℕ) (i j : Fin (n + 1)) :
    |wilkinsonMatrix n 1 i j| ≤ 1 := by
  simp only [wilkinsonMatrix]
  split_ifs <;> norm_num

/-- In every positive dimension there is an input bounded entrywise by one
whose computed upper factor contains an entry of magnitude `2^(N-1)`.
Together with `abs_luPartialPivot_upper_le_two_pow`, this proves sharpness of
the worst-case partial-pivoting growth bound.
atlas: lu-growth-factor (partial) -/
theorem exists_luPartialPivot_growth_eq_two_pow (n : ℕ) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      (∀ i j, |A i j| ≤ 1) ∧
      |(luPartialPivot A).2.2 (Fin.last n) (Fin.last n)| = 2 ^ n := by
  refine ⟨wilkinsonMatrix n 1, abs_wilkinsonMatrix_one_le n, ?_⟩
  rw [luPartialPivot_wilkinsonMatrix_last, mul_one, abs_of_nonneg (by positivity)]

end NLAlib
