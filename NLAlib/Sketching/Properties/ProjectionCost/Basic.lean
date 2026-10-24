import NLAlib.Matrix.Subspaces.ProjectionCosts
import NLAlib.Matrix.Subspaces.RangeProjector
import NLAlib.Matrix.Subspaces.ProjectorTrace

/-!
# Projection-cost preservation with one fixed offset

The source's exact-rank contract is retained. Both lower and upper constants
are explicit, so the two-sided and one-sided forms share one interface.
Source: Cohen–Elder–Musco–Musco–Persu 2015, Definitions 1–2.
Atlas: `projection-cost-preserving-def`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n l : Type*}
  [Fintype m] [Fintype n] [Fintype l] [DecidableEq m]

/-- A fixed nonnegative offset certifies the costs of every rank-exactly-`k`
orthogonal projector. The offset is chosen before the projector. The usual
two-sided constants are `1 - ε, 1 + ε`; the one-sided constants are `1, 1 + ε`.
Cohen–Elder–Musco–Musco–Persu 2015, Definitions 1–2, extended to complex matrices.
atlas: projection-cost-preserving-def -/
def IsProjectionCostPreservingWithOffset (A : Matrix m n 𝕜) (B : Matrix m l 𝕜)
    (k : ℕ) (a b c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ P : Matrix m m 𝕜, IsStarProjection P → P.rank = k →
    a * frobSq ((1 - P) * A) ≤ frobSq ((1 - P) * B) + c ∧
      frobSq ((1 - P) * B) + c ≤ b * frobSq ((1 - P) * A)

/-- A projection-cost-preserving sketch has a single nonnegative offset
working uniformly for all rank-exactly-`k` orthogonal projectors.
Cohen–Elder–Musco–Musco–Persu 2015, Definitions 1–2; complex extension.
atlas: projection-cost-preserving-def -/
def IsProjectionCostPreserving (A : Matrix m n 𝕜) (B : Matrix m l 𝕜)
    (k : ℕ) (a b : ℝ) : Prop :=
  ∃ c, IsProjectionCostPreservingWithOffset A B k a b c

/-- Changing a sketch factor without changing its Gram matrix preserves the
same offset and projection-cost certificate. -/
theorem isProjectionCostPreservingWithOffset_iff_of_gram_eq
    {p : Type*} [Fintype p] {A : Matrix m n 𝕜} {B : Matrix m l 𝕜}
    {C : Matrix m p 𝕜} (h : B * Bᴴ = C * Cᴴ) {k : ℕ} {a b c : ℝ} :
    IsProjectionCostPreservingWithOffset A B k a b c ↔
      IsProjectionCostPreservingWithOffset A C k a b c := by
  simp only [IsProjectionCostPreservingWithOffset,
    frobSq_mul_eq_of_mul_conjTranspose_eq h]

/-- The frame residual is precisely the residual of its orthogonal projector,
so the PCP contract applies without a second notion of cost. -/
theorem frobSq_projResidual_eq_frobSq_one_sub_mul {r : Type*} [Fintype r]
    (Q : Matrix m r 𝕜) (A : Matrix m n 𝕜) :
    frobSq (projResidual Q A) = frobSq ((1 - Q * Qᴴ) * A) := by
  rw [residual_eq_one_sub_mul]

end NLAlib
