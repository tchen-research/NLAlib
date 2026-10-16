import NLAlib.Matrix.Functions.SteinPartialSums

/-! # Actual concatenated factors in Smith doubling -/
noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {K n s : Type*} [RCLike K] [Fintype n] [Fintype s] [DecidableEq n]

/-- The actual doubling factor's recursively doubled column index. -/
def SmithFactorIndex (s : Type*) : ℕ → Type _
  | 0 => s
  | j + 1 => Sum (SmithFactorIndex s j) (SmithFactorIndex s j)

instance smithFactorIndexFintype (j : ℕ) : Fintype (SmithFactorIndex s j) := by
  induction j with
  | zero => exact inferInstanceAs (Fintype s)
  | succ j hj => exact inferInstanceAs (Fintype (Sum (SmithFactorIndex s j) (SmithFactorIndex s j)))

/-- The actual Smith factor starts at `B` and concatenates its propagated
copy at each doubling step. -/
def smithDoublingFactor (A : Matrix n n K) (B : Matrix n s K) :
    (j : ℕ) → Matrix n (SmithFactorIndex s j) K
  | 0 => B
  | j + 1 => Matrix.fromCols (smithDoublingFactor A B j)
      ((smithDoubling A (B * Bᴴ) j).1 * smithDoublingFactor A B j)

/-- The uncompressed concatenated factor represents exactly the actual Smith
iterate at every step. Source: user derivations, factored Smith doubling.
atlas: stein-gramian-smith-doubling -/
theorem smithDoublingFactor_mul_conjTranspose (A : Matrix n n K) (B : Matrix n s K) (j : ℕ) :
    smithDoublingFactor A B j * (smithDoublingFactor A B j)ᴴ =
      (smithDoubling A (B * Bᴴ) j).2 := by
  induction j with
  | zero => rfl
  | succ j hj =>
    rw [smithDoublingFactor, ← smithDoubling_factor_step, hj]
    rfl

/-- Without compression, the actual factor has exactly `2^j * s` columns. -/
theorem card_smithFactorIndex (j : ℕ) : Fintype.card (SmithFactorIndex s j) = 2 ^ j * Fintype.card s := by
  induction j with
  | zero => change Fintype.card s = 2 ^ 0 * Fintype.card s; simp
  | succ j hj =>
    change Fintype.card (Sum (SmithFactorIndex s j) (SmithFactorIndex s j)) = _
    rw [Fintype.card_sum, hj, pow_succ]
    ring

end NLAlib
