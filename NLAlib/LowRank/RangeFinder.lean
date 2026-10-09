import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Interval.Finset.Nat
import NLAlib.Matrix.Norms
import NLAlib.Matrix.Projections
import NLAlib.Matrix.Pseudoinverse

/-!
# The deterministic range-finder bound (Frobenius form)

Halko–Martinsson–Tropp, *Finding structure with randomness*, SIAM Rev. 2011, Theorem 9.1 in
Frobenius form: for a block SVD `A = U₁ Σ₁ V₁ᵀ + U₂ Σ₂ V₂ᵀ`, a test matrix `Ω`, `Ω₁ = V₁ᵀ Ω` of
full row rank, `Ω₂ = V₂ᵀ Ω`, and `Q` with orthonormal columns whose range contains `range(AΩ)`,

  `‖(I − QQᵀ)A‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂ Ω₂ Ω₁†‖_F²`.

Also the rank-`k` truncated variant `‖A − Q⟦QᵀA⟧ₖ‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂ Ω₂ Ω₁†‖_F²`
(Chen–Persson, *One- and two-pass algorithms for low-rank approximation*, Prop. `prop:hmt-struct`)
and the singular-value tail inequality `σ_{ℓ+1}² ≤ (4/t) Σ_{j>k} σ_j²` (same paper, `eq:tGN-tail`).

Ported from the LRA project, `LRA/Deterministic/RangeFinder.lean` (Chen–Persson formalization,
same Mathlib pin), with the helper lemmas from `LRA/Basic.lean`.

## Conventions

* `Σ` is not an identifier, so `Σ₁, Σ₂` are `S₁, S₂`. No diagonality of `S₁, S₂`, no
  orthonormality of `U₁`, no `U₁ᵀU₂ = 0` and no completeness `V₁V₁ᵀ + V₂V₂ᵀ = I` is used, so
  none is assumed (the statements are therefore slightly more general than HMT's).
* The orthonormality hypotheses are matrix equations (`U₂ᵀ * U₂ = 1`, `V₁ᵀ * V₂ = 0`, …).
* `Ω₁` has full row rank is `IsUnit (Ω₁ * Ω₁ᵀ)` and `Ω₁† = pinvR Ω₁`.
* `range(AΩ) ⊆ range(Q)` is `Q * (Qᵀ * (A * Ω)) = A * Ω`.

Atlas: `hmt-9-1-frobenius`, `sigma-tail-bound`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

/-! ### Helpers

These Frobenius-norm and projector facts belong in `NLAlib/Matrix/Norms.lean` and
`NLAlib/Matrix/Projections.lean` and should be consolidated there. They live in the namespace
`NLAlib.RangeFinderAux` so they cannot clash with the versions being added to those files. -/

namespace RangeFinderAux

section Helpers

variable {m n p p' : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype p']

/-- Helper (consolidate into `Norms.lean`): `⟨A + B, C⟩_F = ⟨A, C⟩_F + ⟨B, C⟩_F`. -/
theorem frobInner_add_left (A B C : Matrix m n ℝ) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  unfold frobInner
  simp [add_mul, Finset.sum_add_distrib]

/-- Helper (consolidate into `Norms.lean`): `⟨A, B + C⟩_F = ⟨A, B⟩_F + ⟨A, C⟩_F`. -/
theorem frobInner_add_right (A B C : Matrix m n ℝ) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  rw [frobInner_comm, frobInner_add_left, frobInner_comm B, frobInner_comm C]

/-- Helper (consolidate into `Norms.lean`): `⟨A − B, C⟩_F = ⟨A, C⟩_F − ⟨B, C⟩_F`. -/
theorem frobInner_sub_left (A B C : Matrix m n ℝ) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  unfold frobInner
  simp [sub_mul, Finset.sum_sub_distrib]

/-- Helper (consolidate into `Norms.lean`): `⟨A, B − C⟩_F = ⟨A, B⟩_F − ⟨A, C⟩_F`. -/
theorem frobInner_sub_right (A B C : Matrix m n ℝ) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  rw [frobInner_comm, frobInner_sub_left, frobInner_comm B, frobInner_comm C]

/-- Pythagoras: orthogonal summands have additive squared Frobenius norms. -/
theorem frobSq_add_of_frobInner_eq_zero (A B : Matrix m n ℝ) (h : frobInner A B = 0) :
    frobSq (A + B) = frobSq A + frobSq B := by
  unfold frobSq
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right, frobInner_comm B A, h]
  ring

/-- Helper (consolidate into `Norms.lean`): Pythagoras for a difference. -/
theorem frobSq_sub_of_frobInner_eq_zero (A B : Matrix m n ℝ) (h : frobInner A B = 0) :
    frobSq (A - B) = frobSq A + frobSq B := by
  unfold frobSq
  rw [frobInner_sub_left, frobInner_sub_right, frobInner_sub_right, frobInner_comm B A, h]
  ring

/-- The Frobenius inner product is invariant under transposing both arguments. -/
theorem frobInner_transpose (A B : Matrix m n ℝ) : frobInner Aᵀ Bᵀ = frobInner A B := by
  unfold frobInner
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Helper (consolidate into `Norms.lean`): `‖Aᵀ‖_F² = ‖A‖_F²`. -/
theorem frobSq_transpose (A : Matrix m n ℝ) : frobSq Aᵀ = frobSq A :=
  frobInner_transpose A A

/-- Orthogonal column spaces give Frobenius-orthogonal matrices. -/
theorem frobInner_mul_mul_eq_zero (P : Matrix m p ℝ) (X : Matrix p n ℝ)
    (Q : Matrix m p' ℝ) (Y : Matrix p' n ℝ) (h : Pᵀ * Q = 0) :
    frobInner (P * X) (Q * Y) = 0 := by
  rw [frobInner_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, h]
  simp

/-- Left multiplication by a matrix with orthonormal columns preserves `frobSq`. -/
theorem frobSq_mul_left_of_orthonormal [DecidableEq p] (Q : Matrix m p ℝ) (hQ : Qᵀ * Q = 1)
    (X : Matrix p n ℝ) : frobSq (Q * X) = frobSq X := by
  unfold frobSq
  rw [frobInner_eq_trace, frobInner_eq_trace, Matrix.transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]

/-- Right multiplication by `Vᵀ`, `V` with orthonormal columns, preserves `frobSq`. -/
theorem frobSq_mul_right_of_orthonormal [DecidableEq p] (V : Matrix n p ℝ) (hV : Vᵀ * V = 1)
    (X : Matrix m p ℝ) : frobSq (X * Vᵀ) = frobSq X := by
  rw [← frobSq_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
    frobSq_mul_left_of_orthonormal V hV, frobSq_transpose]

/-- `(I − QQᵀ)ᵀ Q = 0` for `Q` with orthonormal columns. -/
theorem one_sub_mul_transpose_transpose_mul [DecidableEq m] [DecidableEq p] (Q : Matrix m p ℝ)
    (hQ : Qᵀ * Q = 1) : (1 - Q * Qᵀ)ᵀ * Q = 0 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQ, Matrix.mul_one, sub_self]

/-- Pythagoras for the projector `QQᵀ`: for every `B`,
`‖A − QB‖_F² = ‖(I − QQᵀ)A‖_F² + ‖QᵀA − B‖_F²`. -/
theorem frobSq_sub_mul_eq [DecidableEq m] [DecidableEq p] (A : Matrix m n ℝ) (Q : Matrix m p ℝ)
    (hQ : Qᵀ * Q = 1) (B : Matrix p n ℝ) :
    frobSq (A - Q * B) = frobSq (residual Q A) + frobSq (Qᵀ * A - B) := by
  have hdecomp : A - Q * B = (1 - Q * Qᵀ) * A + Q * (Qᵀ * A - B) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_assoc]; abel
  have hperp : residual Q A = (1 - Q * Qᵀ) * A := by
    rw [residual, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  have horth : frobInner ((1 - Q * Qᵀ) * A) (Q * (Qᵀ * A - B)) = 0 :=
    frobInner_mul_mul_eq_zero _ _ _ _ (one_sub_mul_transpose_transpose_mul Q hQ)
  rw [hdecomp, hperp, frobSq_add_of_frobInner_eq_zero _ _ horth,
    frobSq_mul_left_of_orthonormal Q hQ]

end Helpers

end RangeFinderAux

/-! ### The range finder -/

section RangeFinder

variable {m n k r r' t q : ℕ}

/-- `AΩ = U₁Σ₁Ω₁ + U₂Σ₂Ω₂` with `Ω₁ = V₁ᵀΩ`, `Ω₂ = V₂ᵀΩ` (HMT 2011, proof of Thm 9.1).
Atlas `hmt-9-1-frobenius`. -/
theorem rangeFinder_mul_decomp {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (Ω : Matrix (Fin n) (Fin t) ℝ) :
    A * Ω = U₁ * S₁ * (V₁ᵀ * Ω) + U₂ * S₂ * (V₂ᵀ * Ω) := by
  rw [hA, Matrix.add_mul, Matrix.mul_assoc (U₁ * S₁), Matrix.mul_assoc (U₂ * S₂)]

/-- The rank-`≤ k` competitor `Z = AΩΩ₁†V₁ᵀ` satisfies `A − Z = U₂Σ₂V₂ᵀ − U₂Σ₂Ω₂Ω₁†V₁ᵀ`
and hence `‖A − Z‖_F² = ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²` (HMT 2011, proof of Thm 9.1; Chen–Persson,
proof of `prop:hmt-struct`). Atlas `hmt-9-1-frobenius`. -/
theorem frobSq_sub_rangeFinderZ {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : U₂ᵀ * U₂ = 1)
    (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1) (hV : V₁ᵀ * V₂ = 0)
    {Ω : Matrix (Fin n) (Fin t) ℝ} {Ω₁ : Matrix (Fin k) (Fin t) ℝ}
    {Ω₂ : Matrix (Fin r') (Fin t) ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ)) :
    frobSq (A - A * Ω * pinvR Ω₁ * V₁ᵀ) = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  have hZ : A * Ω * pinvR Ω₁ * V₁ᵀ = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ := by
    rw [rangeFinder_mul_decomp hA Ω, ← hΩ₁, ← hΩ₂, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_assoc (U₁ * S₁) Ω₁, mul_pinvR hunit, Matrix.mul_one]
  rw [hZ]
  have hdiff : A - (U₁ * S₁ * V₁ᵀ + U₂ * S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ)
      = U₂ * (S₂ * V₂ᵀ - S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ) := by
    rw [hA, Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    abel
  have hV' : V₂ᵀ * V₁ = 0 := by
    have := congrArg Matrix.transpose hV
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this
  have horth : frobInner (S₂ * V₂ᵀ) (S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ) = 0 := by
    rw [← RangeFinderAux.frobInner_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact RangeFinderAux.frobInner_mul_mul_eq_zero _ _ _ _ hV'
  rw [hdiff, RangeFinderAux.frobSq_mul_left_of_orthonormal U₂ hU₂,
    RangeFinderAux.frobSq_sub_of_frobInner_eq_zero _ _ horth,
    RangeFinderAux.frobSq_mul_right_of_orthonormal V₂ hV₂,
    RangeFinderAux.frobSq_mul_right_of_orthonormal V₁ hV₁]

/-- **Deterministic range-finder bound, Frobenius form** (HMT 2011, Thm 9.1, squared Frobenius
case): if `A = U₁Σ₁V₁ᵀ + U₂Σ₂V₂ᵀ`, `Ω₁ = V₁ᵀΩ` has full row rank, `Ω₂ = V₂ᵀΩ`, `QᵀQ = I` and
`range(AΩ) ⊆ range(Q)`, then `‖(I − QQᵀ)A‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²`.

Deviations from the printed statement: the SVD is a block decomposition with only the
hypotheses the proof uses (`U₂ᵀU₂ = I`, `V₁ᵀV₁ = I`, `V₂ᵀV₂ = I`, `V₁ᵀV₂ = 0`; no diagonality,
no conditions on `U₁`); `P_Y` is `QQᵀ` for any orthonormal `Q` with `range(AΩ) ⊆ range(Q)`
(HMT take `range Q = range(AΩ)`). Atlas `hmt-9-1-frobenius`. -/
theorem rangeFinder_frobSq_le {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : U₂ᵀ * U₂ = 1)
    (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1) (hV : V₁ᵀ * V₂ = 0)
    {Ω : Matrix (Fin n) (Fin t) ℝ} {Ω₁ : Matrix (Fin k) (Fin t) ℝ}
    {Ω₂ : Matrix (Fin r') (Fin t) ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ))
    {Q : Matrix (Fin m) (Fin q) ℝ} (hQo : Qᵀ * Q = 1) (hQ : Q * (Qᵀ * (A * Ω)) = A * Ω) :
    frobSq (residual Q A) ≤ frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  set Z := A * Ω * pinvR Ω₁ * V₁ᵀ
  have hZ : Q * (Qᵀ * Z) = Z := by
    have : Z = A * Ω * (pinvR Ω₁ * V₁ᵀ) := Matrix.mul_assoc _ _ _
    rw [this, ← Matrix.mul_assoc Qᵀ, ← Matrix.mul_assoc Q, hQ]
  calc frobSq (residual Q A)
      ≤ frobSq (residual Q A) + frobSq (Qᵀ * A - Qᵀ * Z) :=
        le_add_of_nonneg_right (frobSq_nonneg _)
    _ = frobSq (A - Q * (Qᵀ * Z)) := (RangeFinderAux.frobSq_sub_mul_eq A Q hQo _).symm
    _ = frobSq (A - Z) := by rw [hZ]
    _ = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) :=
        frobSq_sub_rangeFinderZ hA hU₂ hV₁ hV₂ hV hΩ₁ hΩ₂ hunit

/-- **Truncated range-finder bound** (Chen–Persson, Prop. `prop:hmt-struct`, third inequality;
LRA `hmt_third`): under the hypotheses of `rangeFinder_frobSq_le`, for any best rank-`k`
approximation `Y` of `QᵀA`, `‖A − QY‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²`. Here `k` is the number of
columns of `V₁`. Atlas `hmt-9-1-frobenius` (truncated variant). -/
theorem rangeFinder_truncated_frobSq_le {A : Matrix (Fin m) (Fin n) ℝ}
    {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : U₂ᵀ * U₂ = 1)
    (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1) (hV : V₁ᵀ * V₂ = 0)
    {Ω : Matrix (Fin n) (Fin t) ℝ} {Ω₁ : Matrix (Fin k) (Fin t) ℝ}
    {Ω₂ : Matrix (Fin r') (Fin t) ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ))
    {Q : Matrix (Fin m) (Fin q) ℝ} (hQo : Qᵀ * Q = 1) (hQ : Q * (Qᵀ * (A * Ω)) = A * Ω)
    {Y : Matrix (Fin q) (Fin n) ℝ} (hY : IsBestRankApprox k (Qᵀ * A) Y) :
    frobSq (A - Q * Y) ≤ frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  set Z := A * Ω * pinvR Ω₁ * V₁ᵀ
  have hZ : Q * (Qᵀ * Z) = Z := by
    have : Z = A * Ω * (pinvR Ω₁ * V₁ᵀ) := Matrix.mul_assoc _ _ _
    rw [this, ← Matrix.mul_assoc Qᵀ, ← Matrix.mul_assoc Q, hQ]
  have hZrank : (Qᵀ * Z).rank ≤ k :=
    (Matrix.rank_mul_le_right _ _).trans <| (Matrix.rank_mul_le_right _ _).trans
      ((Matrix.rank_le_card_height _).trans (Fintype.card_fin k).le)
  calc frobSq (A - Q * Y) ≤ frobSq (A - Q * (Qᵀ * Z)) := by
        rw [RangeFinderAux.frobSq_sub_mul_eq A Q hQo Y,
          RangeFinderAux.frobSq_sub_mul_eq A Q hQo (Qᵀ * Z)]
        exact add_le_add le_rfl (hY.2 _ hZrank)
    _ = frobSq (A - Z) := by rw [hZ]
    _ = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) :=
        frobSq_sub_rangeFinderZ hA hU₂ hV₁ hV₂ hV hΩ₁ hΩ₂ hunit

end RangeFinder

/-! ### The singular-value tail inequality

Stated for an arbitrary nonincreasing nonnegative sequence `σ : ℕ → ℝ` indexed from `0`, so
`σ j` is the paper's `σ_{j+1}`, `∑_{j=k+1}^{ℓ} σ_j²` is `∑ j ∈ Finset.Ico k ℓ, σ j ^ 2` and
`σ_{ℓ+1}` is `σ ℓ`. -/

section Tail

/-- `(ℓ − k) σ_{ℓ+1}² ≤ ∑_{j=k+1}^{ℓ} σ_j²` for a nonincreasing nonnegative sequence
(Chen–Persson `eq:tGN-tail`, first inequality multiplied out). Atlas `sigma-tail-bound`. -/
theorem sum_Ico_sq_ge (σ : ℕ → ℝ) (hσ : Antitone σ) (hpos : ∀ j, 0 ≤ σ j) {k ℓ : ℕ}
    (hk : k ≤ ℓ) : ((ℓ : ℝ) - k) * σ ℓ ^ 2 ≤ ∑ j ∈ Finset.Ico k ℓ, σ j ^ 2 := by
  have h1 : ∑ _j ∈ Finset.Ico k ℓ, σ ℓ ^ 2 ≤ ∑ j ∈ Finset.Ico k ℓ, σ j ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hjℓ : j ≤ ℓ := (Finset.mem_Ico.1 hj).2.le
    exact pow_le_pow_left₀ (hpos ℓ) (hσ hjℓ) 2
  rwa [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hk] at h1

/-- `σ_{ℓ+1}² ≤ (ℓ − k)⁻¹ ∑_{j=k+1}^{ℓ} σ_j²` for `k < ℓ` (Chen–Persson `eq:tGN-tail`, first
inequality). Atlas `sigma-tail-bound`. -/
theorem sq_le_avg_Ico (σ : ℕ → ℝ) (hσ : Antitone σ) (hpos : ∀ j, 0 ≤ σ j) {k ℓ : ℕ}
    (hk : k < ℓ) : σ ℓ ^ 2 ≤ (∑ j ∈ Finset.Ico k ℓ, σ j ^ 2) / ((ℓ : ℝ) - k) := by
  have hpos' : (0 : ℝ) < (ℓ : ℝ) - k := by
    have : (k : ℝ) < ℓ := by exact_mod_cast hk
    linarith
  rw [le_div_iff₀ hpos', mul_comm]
  exact sum_Ico_sq_ge σ hσ hpos hk.le

/-- **Singular-value tail bound** (Chen–Persson, Lemma `lem:tGN-residual`, `eq:tGN-tail`; LRA
`tail_bound`): for a nonincreasing nonnegative `σ`, `ℓ = ⌈t/2⌉ = (t + 1)/2`, `4k ≤ t`, `0 < t`
and `ℓ ≤ N`, `σ_{ℓ+1}² ≤ (4/t) ∑_{j=k+1}^{N} σ_j²`. With `N = min(m, n)` and `σ` the singular
values the right-hand sum is `‖A − ⟦A⟧ₖ‖_F²`. Atlas `sigma-tail-bound`. -/
theorem tail_bound (σ : ℕ → ℝ) (hσ : Antitone σ) (hpos : ∀ j, 0 ≤ σ j) {k ℓ t N : ℕ}
    (ht : 0 < t) (hℓ : ℓ = (t + 1) / 2) (hk : 4 * k ≤ t) (hN : ℓ ≤ N) :
    σ ℓ ^ 2 ≤ (4 / t) * ∑ j ∈ Finset.Ico k N, σ j ^ 2 := by
  have hlk : (t : ℝ) / 4 ≤ (ℓ : ℝ) - k := by
    have h1 : t ≤ 2 * ℓ := by omega
    have h1' : (t : ℝ) ≤ 2 * ℓ := by exact_mod_cast h1
    have h2 : (4 * k : ℝ) ≤ t := by exact_mod_cast hk
    linarith
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hkℓ : k ≤ ℓ := by omega
  have hmono : ∑ j ∈ Finset.Ico k ℓ, σ j ^ 2 ≤ ∑ j ∈ Finset.Ico k N, σ j ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hN)
      (fun j _ _ => sq_nonneg (σ j))
  have h1 := (sum_Ico_sq_ge σ hσ hpos hkℓ).trans hmono
  have h2 : (t : ℝ) / 4 * σ ℓ ^ 2 ≤ ∑ j ∈ Finset.Ico k N, σ j ^ 2 :=
    (mul_le_mul_of_nonneg_right hlk (sq_nonneg _)).trans h1
  rw [div_mul_eq_mul_div, le_div_iff₀ ht']
  linarith

end Tail

end NLAlib
