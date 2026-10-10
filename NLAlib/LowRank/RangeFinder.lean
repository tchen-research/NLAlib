import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Interval.Finset.Nat
import NLAlib.Matrix.Norms
import NLAlib.Matrix.Projections
import NLAlib.Matrix.Pseudoinverse
import NLAlib.Matrix.SVD

/-!
# The deterministic range-finder bound (Frobenius form)

Halko–Martinsson–Tropp, *Finding structure with randomness*, SIAM Rev. 2011, Theorem 9.1 in
Frobenius form: for a block SVD `A = U₁ Σ₁ V₁ᵀ + U₂ Σ₂ V₂ᵀ`, a test matrix `Ω`, `Ω₁ = V₁ᵀ Ω` of
full row rank, `Ω₂ = V₂ᵀ Ω`, and `Q` with orthonormal columns whose range contains `range(AΩ)`,

  `‖(I − QQᵀ)A‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂ Ω₂ Ω₁†‖_F²`

(`frobSq_residual_le_of_range_subset`). Also the rank-`k` truncated variant
`‖A − Q⟦QᵀA⟧ₖ‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂ Ω₂ Ω₁†‖_F²`
(`frobSq_sub_mul_le_of_isBestRankApprox_of_range_subset`; Chen–Persson, *One- and two-pass
algorithms for low-rank approximation*, Prop. `prop:hmt-struct`) and the singular-value tail
inequality `σ_{ℓ+1}² ≤ (4/t) Σ_{j>k} σ_j²` (`sq_le_four_div_mul_sum_Ico_sq`; same paper,
`eq:tGN-tail`).

Ported from the LRA project, `LRA/Deterministic/RangeFinder.lean` (Chen–Persson formalization,
same Mathlib pin). The Frobenius and projector helpers of the source are the
`NLAlib.Matrix.Norms` and `NLAlib.Matrix.Projections` lemmas.

## Conventions

* `Σ` is not an identifier, so `Σ₁, Σ₂` are `S₁, S₂`. No diagonality of `S₁, S₂`, no
  orthonormality of `U₁`, no `U₁ᵀU₂ = 0` and no completeness `V₁V₁ᵀ + V₂V₂ᵀ = I` is used, so
  none is assumed (the statements are therefore slightly more general than HMT's).
* All index types are arbitrary `Fintype`s except the rank parameter `Fin k` (columns of `V₁`),
  which is a natural number in the truncated bound.
* `Ω₁` has full row rank is `IsUnit (Ω₁ * Ω₁ᵀ)` and `Ω₁† = pinvR Ω₁`.
* `range(AΩ) ⊆ range(Q)` is `Q * (Qᵀ * (A * Ω)) = A * Ω`.

Atlas: `hmt-9-1-frobenius`, `sigma-tail-bound`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

/-! ### The range finder -/

section RangeFinder

variable {m n r r' t q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype r'] [Fintype t]
  [Fintype q] [DecidableEq r] [DecidableEq r'] [DecidableEq q] {k : ℕ}

omit [Fintype m] [Fintype t] [Fintype q] [DecidableEq r] [DecidableEq r'] [DecidableEq q] in
/-- `AΩ = U₁Σ₁Ω₁ + U₂Σ₂Ω₂` with `Ω₁ = V₁ᵀΩ`, `Ω₂ = V₂ᵀΩ` (HMT 2011, proof of Thm 9.1).
Atlas `hmt-9-1-frobenius`. -/
theorem mul_eq_mul_add_mul_of_eq_add {A : Matrix m n ℝ} {U₁ : Matrix m (Fin k) ℝ}
    {U₂ : Matrix m r ℝ} {V₁ : Matrix n (Fin k) ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (Ω : Matrix n t ℝ) :
    A * Ω = U₁ * S₁ * (V₁ᵀ * Ω) + U₂ * S₂ * (V₂ᵀ * Ω) := by
  rw [hA, Matrix.add_mul, Matrix.mul_assoc (U₁ * S₁), Matrix.mul_assoc (U₂ * S₂)]

omit [Fintype q] [DecidableEq q] in
/-- The rank-`≤ k` competitor `Z = AΩΩ₁†V₁ᵀ` satisfies `A − Z = U₂Σ₂V₂ᵀ − U₂Σ₂Ω₂Ω₁†V₁ᵀ`
and hence `‖A − Z‖_F² = ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²` (HMT 2011, proof of Thm 9.1; Chen–Persson,
proof of `prop:hmt-struct`). Atlas `hmt-9-1-frobenius`.
atlas: hmt-9-1-frobenius -/
theorem frobSq_sub_mul_pinvR_mul_transpose_eq {A : Matrix m n ℝ} {U₁ : Matrix m (Fin k) ℝ}
    {U₂ : Matrix m r ℝ} {V₁ : Matrix n (Fin k) ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    {Ω : Matrix n t ℝ} {Ω₁ : Matrix (Fin k) t ℝ} {Ω₂ : Matrix r' t ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ)) :
    frobSq (A - A * Ω * pinvR Ω₁ * V₁ᵀ) = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  have hZ : A * Ω * pinvR Ω₁ * V₁ᵀ = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ := by
    rw [mul_eq_mul_add_mul_of_eq_add hA Ω, ← hΩ₁, ← hΩ₂, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_assoc (U₁ * S₁) Ω₁, mul_pinvR hunit, Matrix.mul_one]
  rw [hZ]
  have hdiff : A - (U₁ * S₁ * V₁ᵀ + U₂ * S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ)
      = U₂ * (S₂ * V₂ᵀ - S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ) := by
    rw [hA, Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    abel
  have horth : frobInner (S₂ * V₂ᵀ) (S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ) = 0 := by
    rw [← frobInner_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact frobInner_mul_mul_eq_zero _ _ _ _ (transpose_mul_eq_zero_comm.1 hV)
  rw [hdiff, frobSq_mul_left_of_orthonormal hU₂, frobSq_sub_of_frobInner_eq_zero _ _ horth,
    frobSq_mul_right_of_orthonormal hV₂, frobSq_mul_right_of_orthonormal hV₁]

omit [DecidableEq q] in
/-- The competitor `Z = AΩΩ₁†V₁ᵀ` of the range-finder proof lies in `range Q` when
`range(AΩ) ⊆ range(Q)`. Proof-local scaffolding. -/
private theorem mul_transpose_mul_competitor {A : Matrix m n ℝ} {Ω : Matrix n t ℝ}
    {Ω₁ : Matrix (Fin k) t ℝ} {V₁ : Matrix n (Fin k) ℝ} {Q : Matrix m q ℝ}
    (hQ : Q * (Qᵀ * (A * Ω)) = A * Ω) :
    Q * (Qᵀ * (A * Ω * pinvR Ω₁ * V₁ᵀ)) = A * Ω * pinvR Ω₁ * V₁ᵀ := by
  have : A * Ω * pinvR Ω₁ * V₁ᵀ = A * Ω * (pinvR Ω₁ * V₁ᵀ) := Matrix.mul_assoc _ _ _
  rw [this, ← Matrix.mul_assoc Qᵀ, ← Matrix.mul_assoc Q, hQ]

/-- **Deterministic range-finder bound, Frobenius form** (HMT 2011, Thm 9.1, squared Frobenius
case): if `A = U₁Σ₁V₁ᵀ + U₂Σ₂V₂ᵀ`, `Ω₁ = V₁ᵀΩ` has full row rank, `Ω₂ = V₂ᵀΩ`, `QᵀQ = I` and
`range(AΩ) ⊆ range(Q)`, then `‖(I − QQᵀ)A‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²`.
Chen–Persson, Prop. `prop:hmt-struct`, second inequality (LRA `hmt_second_frob`).

Deviations from the printed statement: the SVD is a block decomposition with only the
hypotheses the proof uses (`U₂ᵀU₂ = I`, `V₁ᵀV₁ = I`, `V₂ᵀV₂ = I`, `V₁ᵀV₂ = 0`; no diagonality,
no conditions on `U₁`); `P_Y` is `QQᵀ` for any orthonormal `Q` with `range(AΩ) ⊆ range(Q)`
(HMT take `range Q = range(AΩ)`); index types are arbitrary `Fintype`s. Atlas
`hmt-9-1-frobenius`.
atlas: hmt-9-1-frobenius -/
theorem frobSq_residual_le_of_range_subset {A : Matrix m n ℝ} {U₁ : Matrix m (Fin k) ℝ}
    {U₂ : Matrix m r ℝ} {V₁ : Matrix n (Fin k) ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    {Ω : Matrix n t ℝ} {Ω₁ : Matrix (Fin k) t ℝ} {Ω₂ : Matrix r' t ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ))
    {Q : Matrix m q ℝ} (hQo : HasOrthonormalCols Q) (hQ : Q * (Qᵀ * (A * Ω)) = A * Ω) :
    frobSq (residual Q A) ≤ frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  calc frobSq (residual Q A)
      ≤ frobSq (A - Q * (Qᵀ * (A * Ω * pinvR Ω₁ * V₁ᵀ))) :=
        frobSq_residual_le_frobSq_sub_mul hQo A _
    _ = frobSq (A - A * Ω * pinvR Ω₁ * V₁ᵀ) := by rw [mul_transpose_mul_competitor hQ]
    _ = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) :=
        frobSq_sub_mul_pinvR_mul_transpose_eq hA hU₂ hV₁ hV₂ hV hΩ₁ hΩ₂ hunit

/-- **Truncated range-finder bound** (Chen–Persson, Prop. `prop:hmt-struct`, third inequality;
LRA `hmt_third`): under the hypotheses of `frobSq_residual_le_of_range_subset`, for any best
rank-`k` approximation `Y` of `QᵀA`, `‖A − QY‖_F² ≤ ‖Σ₂‖_F² + ‖Σ₂Ω₂Ω₁†‖_F²`. Here `k` is the
number of columns of `V₁`. Deviation: index types other than `Fin k` are arbitrary `Fintype`s.
Atlas `hmt-9-1-frobenius` (truncated variant).
atlas: hmt-9-1-frobenius -/
theorem frobSq_sub_mul_le_of_isBestRankApprox_of_range_subset {A : Matrix m n ℝ}
    {U₁ : Matrix m (Fin k) ℝ} {U₂ : Matrix m r ℝ} {V₁ : Matrix n (Fin k) ℝ}
    {V₂ : Matrix n r' ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    {Ω : Matrix n t ℝ} {Ω₁ : Matrix (Fin k) t ℝ} {Ω₂ : Matrix r' t ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ))
    {Q : Matrix m q ℝ} (hQo : HasOrthonormalCols Q) (hQ : Q * (Qᵀ * (A * Ω)) = A * Ω)
    {Y : Matrix q n ℝ} (hY : IsBestRankApprox k (Qᵀ * A) Y) :
    frobSq (A - Q * Y) ≤ frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) := by
  have hZrank : (Qᵀ * (A * Ω * pinvR Ω₁ * V₁ᵀ)).rank ≤ k :=
    (Matrix.rank_mul_le_right _ _).trans <| (Matrix.rank_mul_le_right _ _).trans
      ((Matrix.rank_le_card_height _).trans (Fintype.card_fin k).le)
  calc frobSq (A - Q * Y) ≤ frobSq (A - Q * (Qᵀ * (A * Ω * pinvR Ω₁ * V₁ᵀ))) :=
        frobSq_sub_mul_le_of_isBestRankApprox hQo hY _ hZrank
    _ = frobSq (A - A * Ω * pinvR Ω₁ * V₁ᵀ) := by rw [mul_transpose_mul_competitor hQ]
    _ = frobSq S₂ + frobSq (S₂ * Ω₂ * pinvR Ω₁) :=
        frobSq_sub_mul_pinvR_mul_transpose_eq hA hU₂ hV₁ hV₂ hV hΩ₁ hΩ₂ hunit

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
theorem sq_singularValues_le_four_div_mul_sum_Ico_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {k ℓ t N : ℕ} (ht : 0 < t) (hℓ : ℓ = (t + 1) / 2) (hk : 4 * k ≤ t) (hN : ℓ ≤ N) :
    singularValues A ℓ ^ 2 ≤ (4 / t) * ∑ j ∈ Finset.Ico k N, singularValues A j ^ 2 :=
  sq_le_four_div_mul_sum_Ico_sq _ (singularValues_antitone A) (singularValues_nonneg A) ht hℓ
    hk hN

end Tail

end NLAlib
