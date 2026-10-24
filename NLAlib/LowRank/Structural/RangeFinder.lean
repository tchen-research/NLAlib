/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Subspaces.RangeProjector
import NLAlib.Matrix.Basic.Pseudoinverse
import NLAlib.Matrix.Spectral.SVD
/-!
# The deterministic range-finder bound (Frobenius form)

Halko–Martinsson–Tropp, *Finding structure with randomness*, SIAM Rev. 2011, Theorem 9.1 in
Frobenius form: for a block SVD `A = U₁ Σ₁ V₁ᴴ + U₂ Σ₂ V₂ᴴ`, a test matrix `Ω`, `Ω₁ = V₁ᴴ Ω` of
full row rank, `Ω₂ = V₂ᴴ Ω`, and `Q` with orthonormal columns whose range contains `range(AΩ)`,

  `‖(I − QQᴴ)A‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂ Ω₂ Ω₁†‖_F²`

(`frobSq_residual_le_of_range_subset`). Also the rank-`k` truncated variant
`‖A − Q⟦QᴴA⟧ₖ‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂ Ω₂ Ω₁†‖_F²`
(`frobSq_sub_mul_le_of_isBestFrobRankApprox_of_range_subset`; Chen–Persson, *One- and two-pass
algorithms for low-rank approximation*, Prop. `prop:hmt-struct`) and the singular-value tail
inequality `σ_{ℓ+1}² ≤ (4/t) Σ_{j>k} σ_j²` (`sq_le_four_div_mul_sum_Ico_sq`; same paper,
`eq:tGN-tail`).

Ported from the LRA project, `LRA/Deterministic/RangeFinder.lean` (Chen–Persson formalization,
same Mathlib pin). The matrix statements are generic over real or complex scalar fields; public names with
`transpose` retain their historical spelling and use the adjoint generically. The Frobenius
and projector helpers of the source are the
`NLAlib.Matrix.Norms.Core` and `NLAlib.Matrix.Subspaces.Projections` lemmas.

## Conventions

* `Σ` is not an identifier, so `Σ₁, Σ₂` are `S₁, S₂`. No diagonality of `S₁, S₂`, no
  orthonormality of `U₁`, no `U₁ᴴU₂ = 0` and no completeness `V₁V₁ᴴ + V₂V₂ᴴ = I` is used, so
  none is assumed (the statements are therefore slightly more general than HMT's).
* All index types are arbitrary `Fintype`s except the rank parameter `Fin k` (columns of `V₁`),
  which is a natural number in the truncated bound.
* `Ω₁` has full row rank is `IsUnit (Ω₁ * Ω₁ᴴ)` and `Ω₁† = pinvR Ω₁`.
* `range(AΩ) ⊆ range(Q)` is `Q * (Qᴴ * (A * Ω)) = A * Ω`.

Atlas: `hmt-9-1-frobenius`, `sigma-tail-bound`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The range finder -/

section RangeFinder

variable {m n r r' t q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype r'] [Fintype t]
  [Fintype q] [DecidableEq r] [DecidableEq r'] [DecidableEq q] {k : ℕ}

omit [Fintype m] [Fintype t] [Fintype q] [DecidableEq r] [DecidableEq r'] [DecidableEq q] in
/-- `AΩ = U₁Σ₁Ω₁ + U₂Σ₂Ω₂` with `Ω₁ = V₁ᴴΩ`, `Ω₂ = V₂ᴴΩ` (HMT 2011, proof of Thm 9.1).
Atlas `hmt-9-1-frobenius`. -/
theorem mul_eq_mul_add_mul_of_eq_add {A : Matrix m n 𝕜} {U₁ : Matrix m (Fin k) 𝕜}
    {U₂ : Matrix m r 𝕜} {V₁ : Matrix n (Fin k) 𝕜} {V₂ : Matrix n r' 𝕜}
    {S₁ : Matrix (Fin k) (Fin k) 𝕜} {S₂ : Matrix r r' 𝕜}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ) (Ω : Matrix n t 𝕜) :
    A * Ω = U₁ * S₁ * (V₁ᴴ * Ω) + U₂ * S₂ * (V₂ᴴ * Ω) := by
  rw [hA, Matrix.add_mul, Matrix.mul_assoc (U₁ * S₁), Matrix.mul_assoc (U₂ * S₂)]

omit [Fintype m] [Fintype q] [DecidableEq r] [DecidableEq r'] [DecidableEq q] in
/-- The competitor identity of the range-finder proof: `A − AΩΩ₁†V₁ᴴ = U₂(Σ₂V₂ᴴ − Σ₂Ω₂Ω₁†V₁ᴴ)`
when `A = U₁Σ₁V₁ᴴ + U₂Σ₂V₂ᴴ`, `Ω₁ = V₁ᴴΩ` has full row rank and `Ω₂ = V₂ᴴΩ`. HMT 2011, proof of
Thm 9.1 (§9.2). Atlas `hmt-9-1-spectral`, `hmt-9-1-frobenius`. -/
theorem sub_mul_pinvR_mul_conjTranspose_eq {A : Matrix m n 𝕜} {U₁ : Matrix m (Fin k) 𝕜}
    {U₂ : Matrix m r 𝕜} {V₁ : Matrix n (Fin k) 𝕜} {V₂ : Matrix n r' 𝕜}
    {S₁ : Matrix (Fin k) (Fin k) 𝕜} {S₂ : Matrix r r' 𝕜}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ)
    {Ω : Matrix n t 𝕜} {Ω₁ : Matrix (Fin k) t 𝕜} {Ω₂ : Matrix r' t 𝕜}
    (hΩ₁ : Ω₁ = V₁ᴴ * Ω) (hΩ₂ : Ω₂ = V₂ᴴ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᴴ)) :
    A - A * Ω * pinvR Ω₁ * V₁ᴴ = U₂ * (S₂ * V₂ᴴ - S₂ * Ω₂ * pinvR Ω₁ * V₁ᴴ) := by
  have hZ : A * Ω * pinvR Ω₁ * V₁ᴴ = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * Ω₂ * pinvR Ω₁ * V₁ᴴ := by
    rw [mul_eq_mul_add_mul_of_eq_add hA Ω, ← hΩ₁, ← hΩ₂, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_assoc (U₁ * S₁) Ω₁, mul_pinvR hunit, Matrix.mul_one]
  rw [hZ, hA, Matrix.mul_sub]
  simp only [Matrix.mul_assoc]
  abel

omit [Fintype q] [DecidableEq q] in
/-- The rank-`≤ k` competitor `Z = AΩΩ₁†V₁ᴴ` satisfies `A − Z = U₂Σ₂V₂ᴴ − U₂Σ₂Ω₂Ω₁†V₁ᴴ`
and hence `‖A − Z‖_F² = ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²` (HMT 2011, proof of Thm 9.1; Chen–Persson,
proof of `prop:hmt-struct`). Atlas `hmt-9-1-frobenius`.
atlas: hmt-9-1-frobenius -/
theorem frobSq_sub_mul_pinvR_mul_conjTranspose_eq {A : Matrix m n 𝕜} {U₁ : Matrix m (Fin k) 𝕜}
    {U₂ : Matrix m r 𝕜} {V₁ : Matrix n (Fin k) 𝕜} {V₂ : Matrix n r' 𝕜}
    {S₁ : Matrix (Fin k) (Fin k) 𝕜} {S₂ : Matrix r r' 𝕜}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᴴ * V₂ = 0)
    {Ω : Matrix n t 𝕜} {Ω₁ : Matrix (Fin k) t 𝕜} {Ω₂ : Matrix r' t 𝕜}
    (hΩ₁ : Ω₁ = V₁ᴴ * Ω) (hΩ₂ : Ω₂ = V₂ᴴ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᴴ)) :
    frobSq (A - A * Ω * pinvR Ω₁ * V₁ᴴ) = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  have horth : frobInner (S₂ * V₂ᴴ) (S₂ * Ω₂ * pinvR Ω₁ * V₁ᴴ) = 0 := by
    rw [← frobInner_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact frobInner_mul_mul_eq_zero _ _ _ _ (conjTranspose_mul_eq_zero_comm.1 hV)
  rw [sub_mul_pinvR_mul_conjTranspose_eq hA hΩ₁ hΩ₂ hunit,
    frobSq_mul_left_of_orthonormal hU₂.conjTranspose_mul_self,
    frobSq_sub_of_frobInner_eq_zero _ _ horth,
    frobSq_mul_right_of_orthonormal hV₂.conjTranspose_mul_self,
    frobSq_mul_right_of_orthonormal hV₁.conjTranspose_mul_self]

omit [DecidableEq q] in
/-- The competitor `Z = AΩΩ₁†V₁ᴴ` of the range-finder proof lies in `range Q` when
`range(AΩ) ⊆ range(Q)`. Proof-local scaffolding. -/
private theorem mul_transpose_mul_competitor {A : Matrix m n 𝕜} {Ω : Matrix n t 𝕜}
    {Ω₁ : Matrix (Fin k) t 𝕜} {V₁ : Matrix n (Fin k) 𝕜} {Q : Matrix m q 𝕜}
    (hQ : Q * (Qᴴ * (A * Ω)) = A * Ω) :
    Q * (Qᴴ * (A * Ω * pinvR Ω₁ * V₁ᴴ)) = A * Ω * pinvR Ω₁ * V₁ᴴ := by
  have : A * Ω * pinvR Ω₁ * V₁ᴴ = A * Ω * (pinvR Ω₁ * V₁ᴴ) := Matrix.mul_assoc _ _ _
  rw [this, ← Matrix.mul_assoc Qᴴ, ← Matrix.mul_assoc Q, hQ]

/-- **Deterministic range-finder bound, Frobenius form** (HMT 2011, Thm 9.1, squared Frobenius
case): if `A = U₁Σ₁V₁ᴴ + U₂Σ₂V₂ᴴ`, `Ω₁ = V₁ᴴΩ` has full row rank, `Ω₂ = V₂ᴴΩ`, `QᴴQ = I` and
`range(AΩ) ⊆ range(Q)`, then `‖(I − QQᴴ)A‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²`.
Chen–Persson, Prop. `prop:hmt-struct`, second inequality (LRA `hmt_second_frob`).

Deviations from the printed statement: the SVD is a block decomposition with only the
hypotheses the proof uses (`U₂ᴴU₂ = I`, `V₁ᴴV₁ = I`, `V₂ᴴV₂ = I`, `V₁ᴴV₂ = 0`; no diagonality,
no conditions on `U₁`); `P_Y` is `QQᴴ` for any orthonormal `Q` with `range(AΩ) ⊆ range(Q)`
(HMT take `range Q = range(AΩ)`); index types are arbitrary `Fintype`s. Atlas
`hmt-9-1-frobenius`.
atlas: hmt-9-1-frobenius -/
theorem frobSq_residual_le_of_range_subset {A : Matrix m n 𝕜} {U₁ : Matrix m (Fin k) 𝕜}
    {U₂ : Matrix m r 𝕜} {V₁ : Matrix n (Fin k) 𝕜} {V₂ : Matrix n r' 𝕜}
    {S₁ : Matrix (Fin k) (Fin k) 𝕜} {S₂ : Matrix r r' 𝕜}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᴴ * V₂ = 0)
    {Ω : Matrix n t 𝕜} {Ω₁ : Matrix (Fin k) t 𝕜} {Ω₂ : Matrix r' t 𝕜}
    (hΩ₁ : Ω₁ = V₁ᴴ * Ω) (hΩ₂ : Ω₂ = V₂ᴴ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᴴ))
    {Q : Matrix m q 𝕜} (hQo : HasOrthonormalCols Q) (hQ : Q * (Qᴴ * (A * Ω)) = A * Ω) :
    frobSq (projResidual Q A) ≤ frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  calc frobSq (projResidual Q A)
      ≤ frobSq (A - Q * (Qᴴ * (A * Ω * pinvR Ω₁ * V₁ᴴ))) :=
        frobSq_residual_le_frobSq_sub_mul hQo A _
    _ = frobSq (A - A * Ω * pinvR Ω₁ * V₁ᴴ) := by rw [mul_transpose_mul_competitor hQ]
    _ = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) :=
        frobSq_sub_mul_pinvR_mul_conjTranspose_eq hA hU₂ hV₁ hV₂ hV hΩ₁ hΩ₂ hunit

/-- The actual sampled-range projector satisfies the deterministic Frobenius graph bound,
over real or complex scalars. This avoids selecting a random orthonormal frame.
Source: HMT (2011), Theorem 9.1; atlas `hmt-9-1-frobenius`. -/
theorem frobSq_sub_rangeProjector_mul_le_of_svd_blocks
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m n 𝕜} {U₁ : Matrix m (Fin k) 𝕜}
    {U₂ : Matrix m r 𝕜} {V₁ : Matrix n (Fin k) 𝕜} {V₂ : Matrix n r' 𝕜}
    {S₁ : Matrix (Fin k) (Fin k) 𝕜} {S₂ : Matrix r r' 𝕜}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᴴ * V₂ = 0)
    {Ω : Matrix n t 𝕜} {Ω₁ : Matrix (Fin k) t 𝕜} {Ω₂ : Matrix r' t 𝕜}
    (hΩ₁ : Ω₁ = V₁ᴴ * Ω) (hΩ₂ : Ω₂ = V₂ᴴ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᴴ)) :
    frobSq (A - rangeProjector (A * Ω) * A) ≤
      frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  let C := A * Ω * (pinvR Ω₁ * V₁ᴴ)
  have hfix : rangeProjector (A * Ω) * C = C := by
    change rangeProjector (A * Ω) * ((A * Ω) * (pinvR Ω₁ * V₁ᴴ)) = _
    rw [← Matrix.mul_assoc, rangeProjector_mul]
  have he : A - rangeProjector (A * Ω) * A =
      (A - C) - rangeProjector (A * Ω) * (A - C) := by
    rw [Matrix.mul_sub, hfix]
    abel
  calc
    frobSq (A - rangeProjector (A * Ω) * A) =
        frobSq ((A - C) - rangeProjector (A * Ω) * (A - C)) := congrArg frobSq he
    _ ≤ frobSq (A - C) := frobSq_sub_rangeProjector_mul_le _ _
    _ = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
      change frobSq (A - (A * Ω) * (pinvR Ω₁ * V₁ᴴ)) = _
      rw [← Matrix.mul_assoc]
      exact frobSq_sub_mul_pinvR_mul_conjTranspose_eq hA hU₂ hV₁ hV₂ hV hΩ₁ hΩ₂ hunit

/-- The actual sampled-range projector satisfies the unsquared spectral graph bound over
real or complex scalars. Source: HMT (2011), proof of Theorem 9.1; supports `rsvd-tail`. -/
theorem specNorm_sub_rangeProjector_mul_le_of_svd_blocks
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m n 𝕜} {U₁ : Matrix m (Fin k) 𝕜}
    {U₂ : Matrix m r 𝕜} {V₁ : Matrix n (Fin k) 𝕜} {V₂ : Matrix n r' 𝕜}
    {S₁ : Matrix (Fin k) (Fin k) 𝕜} {S₂ : Matrix r r' 𝕜}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    {Ω : Matrix n t 𝕜} {Ω₁ : Matrix (Fin k) t 𝕜} {Ω₂ : Matrix r' t 𝕜}
    (hΩ₁ : Ω₁ = V₁ᴴ * Ω) (hΩ₂ : Ω₂ = V₂ᴴ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᴴ)) :
    specNorm (A - rangeProjector (A * Ω) * A) ≤
      specNorm S₂ + specNorm (S₂ * Ω₂ * pinvR Ω₁) := by
  let C := A * Ω * (pinvR Ω₁ * V₁ᴴ)
  have hfix : rangeProjector (A * Ω) * C = C := by
    change rangeProjector (A * Ω) * ((A * Ω) * (pinvR Ω₁ * V₁ᴴ)) = _
    rw [← Matrix.mul_assoc, rangeProjector_mul]
  have he : A - rangeProjector (A * Ω) * A =
      (A - C) - rangeProjector (A * Ω) * (A - C) := by
    rw [Matrix.mul_sub, hfix]
    abel
  have hc : A - C = U₂ * (S₂ * V₂ᴴ - S₂ * Ω₂ * pinvR Ω₁ * V₁ᴴ) := by
    dsimp only [C]
    rw [← Matrix.mul_assoc]
    exact sub_mul_pinvR_mul_conjTranspose_eq hA hΩ₁ hΩ₂ hunit
  calc
    specNorm (A - rangeProjector (A * Ω) * A) =
        specNorm ((A - C) - rangeProjector (A * Ω) * (A - C)) := congrArg specNorm he
    _ ≤ specNorm (A - C) := specNorm_sub_rangeProjector_mul_le _ _
    _ = specNorm (S₂ * V₂ᴴ - S₂ * Ω₂ * pinvR Ω₁ * V₁ᴴ) := by
      rw [hc, specNorm_mul_left_of_hasOrthonormalCols hU₂.conjTranspose_mul_self]
    _ ≤ specNorm (S₂ * V₂ᴴ) + specNorm (S₂ * Ω₂ * pinvR Ω₁ * V₁ᴴ) := specNorm_sub_le _ _
    _ = _ := by
      rw [specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hV₂.conjTranspose_mul_self,
        specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hV₁.conjTranspose_mul_self]

/-- **Truncated range-finder bound** (Chen–Persson, Prop. `prop:hmt-struct`, third inequality;
LRA `hmt_third`): under the hypotheses of `frobSq_residual_le_of_range_subset`, for any best
rank-`k` approximation `Y` of `QᴴA`, `‖A − QY‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²`. Here `k` is the
number of columns of `V₁`. Deviation: index types other than `Fin k` are arbitrary `Fintype`s.
Atlas `hmt-9-1-frobenius` (truncated variant).
atlas: hmt-9-1-frobenius -/
theorem frobSq_sub_mul_le_of_isBestFrobRankApprox_of_range_subset {A : Matrix m n 𝕜}
    {U₁ : Matrix m (Fin k) 𝕜} {U₂ : Matrix m r 𝕜} {V₁ : Matrix n (Fin k) 𝕜}
    {V₂ : Matrix n r' 𝕜} {S₁ : Matrix (Fin k) (Fin k) 𝕜} {S₂ : Matrix r r' 𝕜}
    (hA : A = U₁ * S₁ * V₁ᴴ + U₂ * S₂ * V₂ᴴ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᴴ * V₂ = 0)
    {Ω : Matrix n t 𝕜} {Ω₁ : Matrix (Fin k) t 𝕜} {Ω₂ : Matrix r' t 𝕜}
    (hΩ₁ : Ω₁ = V₁ᴴ * Ω) (hΩ₂ : Ω₂ = V₂ᴴ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᴴ))
    {Q : Matrix m q 𝕜} (hQo : HasOrthonormalCols Q) (hQ : Q * (Qᴴ * (A * Ω)) = A * Ω)
    {Y : Matrix q n 𝕜} (hY : IsBestFrobRankApprox (Qᴴ * A) k Y) :
    frobSq (A - Q * Y) ≤ frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  have hZrank : (Qᴴ * (A * Ω * pinvR Ω₁ * V₁ᴴ)).rank ≤ k :=
    (Matrix.rank_mul_le_right _ _).trans <| (Matrix.rank_mul_le_right _ _).trans
      ((Matrix.rank_le_card_height _).trans (Fintype.card_fin k).le)
  calc frobSq (A - Q * Y) ≤ frobSq (A - Q * (Qᴴ * (A * Ω * pinvR Ω₁ * V₁ᴴ))) :=
        frobSq_sub_mul_le_of_isBestFrobRankApprox hQo hY _ hZrank
    _ = frobSq (A - A * Ω * pinvR Ω₁ * V₁ᴴ) := by rw [mul_transpose_mul_competitor hQ]
    _ = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) :=
        frobSq_sub_mul_pinvR_mul_conjTranspose_eq hA hU₂ hV₁ hV₂ hV hΩ₁ hΩ₂ hunit

end RangeFinder

/-! ### The singular-value tail inequality

Stated for an arbitrary nonincreasing nonnegative sequence `σ : ℕ → ℝ` indexed from `0`, so
`σ j` is the paper's `σ_{j+1}`, `∑_{j=k+1}^{ℓ} σ_j²` is `∑ j ∈ Finset.Ico k ℓ, σ j ^ 2` and
`σ_{ℓ+1}` is `σ ℓ`; `sq_singularValues_le_four_div_mul_sum_Ico_sq` specialises to the singular
values of a matrix. -/

section Tail

/-- `(ℓ − k) σ_{ℓ+1}² ≤ ∑_{j=k+1}^{ℓ} σ_j²` for a nonincreasing nonnegative sequence
(Chen–Persson `eq:tGN-tail`, first inequality multiplied out). Atlas `sigma-tail-bound`. -/
theorem sub_mul_sq_le_sum_Ico_sq (σ : ℕ → ℝ) (hσ : Antitone σ) (hpos : ∀ j, 0 ≤ σ j)
    {k ℓ : ℕ} (hk : k ≤ ℓ) : ((ℓ : ℝ) - k) * σ ℓ ^ 2 ≤ ∑ j ∈ Finset.Ico k ℓ, σ j ^ 2 := by
  have h1 : ∑ _j ∈ Finset.Ico k ℓ, σ ℓ ^ 2 ≤ ∑ j ∈ Finset.Ico k ℓ, σ j ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hjℓ : j ≤ ℓ := (Finset.mem_Ico.1 hj).2.le
    exact pow_le_pow_left₀ (hpos ℓ) (hσ hjℓ) 2
  rwa [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hk] at h1

/-- `σ_{ℓ+1}² ≤ (ℓ − k)⁻¹ ∑_{j=k+1}^{ℓ} σ_j²` for `k < ℓ` (Chen–Persson `eq:tGN-tail`, first
inequality). Atlas `sigma-tail-bound`.
atlas: sigma-tail-bound -/
theorem sq_le_sum_Ico_sq_div (σ : ℕ → ℝ) (hσ : Antitone σ) (hpos : ∀ j, 0 ≤ σ j) {k ℓ : ℕ}
    (hk : k < ℓ) : σ ℓ ^ 2 ≤ (∑ j ∈ Finset.Ico k ℓ, σ j ^ 2) / ((ℓ : ℝ) - k) := by
  have hpos' : (0 : ℝ) < (ℓ : ℝ) - k := by
    have : (k : ℝ) < ℓ := by exact_mod_cast hk
    linarith
  rw [le_div_iff₀ hpos', mul_comm]
  exact sub_mul_sq_le_sum_Ico_sq σ hσ hpos hk.le

/-- **Singular-value tail bound** (Chen–Persson, Lemma `lem:tGN-residual`, `eq:tGN-tail`; LRA
`tail_bound`): for a nonincreasing nonnegative `σ`, `ℓ = ⌈t/2⌉ = (t + 1)/2`, `4k ≤ t`, `0 < t`
and `ℓ ≤ N`, `σ_{ℓ+1}² ≤ (4/t) ∑_{j=k+1}^{N} σ_j²`. With `N = min(m, n)` and `σ` the singular
values the right-hand sum is `‖A − ⟦A⟧ₖ‖_F²` (see
`sq_singularValues_le_four_div_mul_sum_Ico_sq`). Atlas `sigma-tail-bound`.
atlas: sigma-tail-bound -/
theorem sq_le_four_div_mul_sum_Ico_sq (σ : ℕ → ℝ) (hσ : Antitone σ) (hpos : ∀ j, 0 ≤ σ j)
    {k ℓ t N : ℕ} (ht : 0 < t) (hℓ : ℓ = (t + 1) / 2) (hk : 4 * k ≤ t) (hN : ℓ ≤ N) :
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
  have h1 := (sub_mul_sq_le_sum_Ico_sq σ hσ hpos hkℓ).trans hmono
  have h2 : (t : ℝ) / 4 * σ ℓ ^ 2 ≤ ∑ j ∈ Finset.Ico k N, σ j ^ 2 :=
    (mul_le_mul_of_nonneg_right hlk (sq_nonneg _)).trans h1
  rw [div_mul_eq_mul_div, le_div_iff₀ ht']
  linarith

/-- The singular-value tail bound for the singular values of a matrix:
`σ_{ℓ+1}(A)² ≤ (4/t) ∑_{j=k+1}^{N} σ_j(A)²` for `ℓ = (t + 1)/2`, `4k ≤ t`, `0 < t`, `ℓ ≤ N`
(Chen–Persson, `eq:tGN-tail`). `sq_le_four_div_mul_sum_Ico_sq` applied to `singularValues A`.
Atlas `sigma-tail-bound` (uses `svd`). -/
theorem sq_singularValues_le_four_div_mul_sum_Ico_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜)
    {k ℓ t N : ℕ} (ht : 0 < t) (hℓ : ℓ = (t + 1) / 2) (hk : 4 * k ≤ t) (hN : ℓ ≤ N) :
    singularValues A ℓ ^ 2 ≤ (4 / t) * ∑ j ∈ Finset.Ico k N, singularValues A j ^ 2 :=
  sq_le_four_div_mul_sum_Ico_sq _ (singularValues_antitone A) (singularValues_nonneg A) ht hℓ
    hk hN

end Tail

end NLAlib
