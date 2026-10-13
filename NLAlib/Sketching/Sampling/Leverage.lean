import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Basic.MoorePenroseProjector
/-!
# Leverage scores

The leverage score of row `i` of a real matrix `A` is the `i`-th diagonal entry of the
orthogonal projector onto `range A`, `ℓᵢ(A) = (A A⁺)ᵢᵢ` (`NLAlib.leverageScore`).

* `leverageScore_nonneg`, `leverageScore_le_one`: `0 ≤ ℓᵢ ≤ 1`;
* `sum_leverageScore_eq_rank`: `∑ᵢ ℓᵢ = rank A`;
* `leverageScore_eq_sum_sq_of_hasOrthonormalCols`: for any orthonormal basis `U` of
  `range A`, `ℓᵢ = ‖U_{i,:}‖²`; in particular the row norms do not depend on the basis.

The basis-independence step is the projector identity
`mul_transpose_eq_mul_moorePenroseInverse` (`NLAlib.Matrix.Basic.MoorePenroseProjector`): if `Q`
has orthonormal columns, `range Y ⊆ range Q` and `rank Y` is at least the number of columns of
`Q`, then `QQᵀ = Y Y⁺`.

Source: Drineas–Mahoney–Muthukrishnan–Woodruff 2012, §1–2; Woodruff 2014, §2.4;
Martinsson–Tropp 2020, §9.6. Atlas: `leverage-scores`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-- The **leverage score** of row `i` of `A`: `ℓᵢ(A) = (A A⁺)ᵢᵢ`, the `i`-th diagonal entry of
the orthogonal projector onto `range A`. Defined for every real matrix (any rank, empty
shapes). Drineas–Mahoney–Muthukrishnan–Woodruff 2012, Def. 1; Woodruff 2014, Def. 2.12.
Atlas `leverage-scores`.
atlas: leverage-scores -/
def leverageScore (A : Matrix m n ℝ) (i : m) : ℝ := (A * moorePenroseInverse A) i i

/-- `0 ≤ ℓᵢ(A)`. Woodruff 2014, §2.4; atlas `leverage-scores`.
atlas: leverage-scores -/
theorem leverageScore_nonneg (A : Matrix m n ℝ) (i : m) : 0 ≤ leverageScore A i :=
  (re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem _
    (Matrix.isHermitian_iff_isSymm.mpr (mul_moorePenroseInverse_isHermitian A))
    (mul_moorePenroseInverse_isIdempotentElem A) i).1

/-- `ℓᵢ(A) ≤ 1`. Woodruff 2014, §2.4; atlas `leverage-scores`.
atlas: leverage-scores -/
theorem leverageScore_le_one (A : Matrix m n ℝ) (i : m) : leverageScore A i ≤ 1 :=
  (re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem _
    (Matrix.isHermitian_iff_isSymm.mpr (mul_moorePenroseInverse_isHermitian A))
    (mul_moorePenroseInverse_isIdempotentElem A) i).2

/-- The leverage scores sum to the rank: `∑ᵢ ℓᵢ(A) = rank A`. Woodruff 2014, §2.4
(for full column rank, `∑ᵢ ℓᵢ = d`); atlas `leverage-scores`.
atlas: leverage-scores -/
theorem sum_leverageScore_eq_rank [DecidableEq m] (A : Matrix m n ℝ) :
    ∑ i, leverageScore A i = (A.rank : ℝ) := by
  rw [← trace_mul_moorePenroseInverse A]
  rfl

/-- **Leverage scores are squared row norms of any orthonormal basis.** If `U` has
orthonormal columns and is a basis of `range A` (`range A ⊆ range U`, written `U (Uᵀ A) = A`,
and `U` has at most `rank A` columns), then `ℓᵢ(A) = ∑ⱼ Uᵢⱼ² = ‖U_{i,:}‖²`. Since the left side
does not mention `U`, the row norms do not depend on the choice of basis.
Drineas–Mahoney–Muthukrishnan–Woodruff 2012, Def. 1 and the remark after it; Woodruff 2014,
Def. 2.12. Atlas `leverage-scores`. Deviation: "orthonormal basis of `range A`" is spelled as the
two hypotheses `hUA`, `hr` (together with orthonormality they force `range U = range A`).
atlas: leverage-scores -/
theorem leverageScore_eq_sum_sq_of_hasOrthonormalCols [DecidableEq m] [DecidableEq q]
    {A : Matrix m n ℝ} {U : Matrix m q ℝ} (hU : HasOrthonormalCols U)
    (hUA : U * (Uᵀ * A) = A) (hr : Fintype.card q ≤ A.rank) (i : m) :
    leverageScore A i = ∑ j, U i j ^ 2 := by
  unfold leverageScore
  rw [← mul_conjTranspose_eq_mul_moorePenroseInverse hU hUA hr, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, star_trivial, sq]

/-- For a matrix `U` with orthonormal columns, `ℓᵢ(U) = ∑ⱼ Uᵢⱼ²`.
Woodruff 2014, §2.4; atlas `leverage-scores`. -/
theorem leverageScore_eq_sum_sq_of_self [DecidableEq m] [DecidableEq q] {U : Matrix m q ℝ}
    (hU : HasOrthonormalCols U) (i : m) : leverageScore U i = ∑ j, U i j ^ 2 := by
  have hUU : U * (Uᵀ * U) = U := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial U, hU.conjTranspose_mul_self,
      Matrix.mul_one]
  have hr : Fintype.card q ≤ U.rank := by
    have h1 : (Uᵀ * U).rank ≤ U.rank := Matrix.rank_mul_le_right _ _
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial U, hU.conjTranspose_mul_self,
      Matrix.rank_one] at h1
    exact h1
  exact leverageScore_eq_sum_sq_of_hasOrthonormalCols hU hUU hr i

end NLAlib
