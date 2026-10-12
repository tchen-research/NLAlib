import Mathlib.Analysis.Matrix.Order
import NLAlib.Matrix.Basic.GramVanishing

/-!
# One step of pivoted Cholesky elimination

`choleskyStep A t = A − A(:,t) A(t,:) / A(t,t)`, the square-root-free rank-one Schur update on
the pivot `t`, total in the pivot (a zero pivot leaves `A` unchanged). Stated over any field;
the positive semidefinite API is over `ℝ`.

* `choleskyStep_apply`: entries `aᵢⱼ − aᵢₜ aₜⱼ / aₜₜ`;
* `posSemidef_choleskyStep`, `posSemidef_sub_choleskyStep`: for PSD `A` the step is PSD and
  decreases `A` in Loewner order, for any pivot;
* `choleskyStep_apply_pivot_left/right`: on a PSD matrix the step zeroes the pivot row and column;
* `ker_mulVecLin_le_ker_choleskyStep`, `rank_choleskyStep_lt`: the kernel grows, and a nonzero
  pivot strictly lowers the rank.

The pivot-history recursion is `partialCholeskyResidual` (LowRank/Cholesky/PartialCholesky); the
step is one-column Nyström, `choleskyStep_eq_sub_nystrom` (LowRank/Cholesky/CholeskyPivot).
Sources: Golub–Van Loan 2013, §4.2.8–4.2.9; Chen–Epperly–Tropp–Webber 2023 (RPCholesky), §2.
Atlas: helper for `partial-cholesky-nystrom` and `rpcholesky`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

section Field

variable {K : Type*} [Field K] {n : Type*}

/-- **One step of (pivoted) Cholesky elimination** on pivot `t`:
`A − A(:,t) A(t,:) / A(t,t)`, the Schur complement of `A(t,t)` padded with a zero row and column
at `t`. Total: for `A(t,t) = 0` it returns `A`. Golub–Van Loan 2013, §4.2.9; CETW 2023, §2.
Stated over any field (over `ℂ` it is `complexCholeskyResidualStep`, by `rfl`). -/
def choleskyStep (A : Matrix n n K) (t : n) : Matrix n n K :=
  A - (A t t)⁻¹ • vecMulVec (fun i => A i t) fun j => A t j

/-- Entrywise form of a Cholesky step: `aᵢⱼ − aᵢₜ aₜⱼ / aₜₜ`. -/
@[simp]
theorem choleskyStep_apply (A : Matrix n n K) (t i j : n) :
    choleskyStep A t i j = A i j - (A t t)⁻¹ * (A i t * A t j) := by
  simp [choleskyStep, vecMulVec_apply]

/-- A zero matrix is absorbing for every pivot index.
Source: manuscript `sa:rp-update`, its absorbing-zero convention. -/
@[simp] theorem choleskyStep_zero (t : n) : choleskyStep (0 : Matrix n n K) t = 0 := by
  ext i j
  simp

/-- A zero diagonal pivot leaves the matrix unchanged. -/
theorem choleskyStep_eq_self_of_apply_self_eq_zero {A : Matrix n n K} {t : n} (ht : A t t = 0) :
    choleskyStep A t = A := by
  simp [choleskyStep, ht]

/-- A nonzero diagonal pivot eliminates its entire row (no positivity needed).
Source: manuscript `sa:rp-update`, rank-termination argument. -/
theorem choleskyStep_apply_pivot_left_of_ne_zero {A : Matrix n n K} {t : n} (ht : A t t ≠ 0)
    (j : n) : choleskyStep A t t j = 0 := by
  rw [choleskyStep_apply, ← mul_assoc, inv_mul_cancel₀ ht, one_mul, sub_self]

/-- A nonzero diagonal pivot eliminates its entire column (no positivity needed). -/
theorem choleskyStep_apply_pivot_right_of_ne_zero {A : Matrix n n K} {t : n} (ht : A t t ≠ 0)
    (i : n) : choleskyStep A t i t = 0 := by
  rw [choleskyStep_apply, mul_comm (A i t), ← mul_assoc, inv_mul_cancel₀ ht, one_mul, sub_self]

/-- A Cholesky step keeps zero rows zero. -/
theorem choleskyStep_apply_eq_zero_of_row {A : Matrix n n K} {u : n} (hu : ∀ j, A u j = 0)
    (t j : n) : choleskyStep A t u j = 0 := by
  simp [hu]

/-- A Cholesky step keeps zero columns zero. -/
theorem choleskyStep_apply_eq_zero_of_col {A : Matrix n n K} {u : n} (hu : ∀ i, A i u = 0)
    (t i : n) : choleskyStep A t i u = 0 := by
  simp [hu]

variable [Fintype n] [DecidableEq n]

/-- A Cholesky step can only enlarge the kernel: `choleskyStep A t = (1 − M) A` with
`M = A(:,t) eₜᵀ / A(t,t)`. Source: manuscript `sa:rp-rank`; CETW (2025), exhaustion of the
column range. -/
theorem ker_mulVecLin_le_ker_choleskyStep (A : Matrix n n K) (t : n) :
    LinearMap.ker A.mulVecLin ≤ LinearMap.ker (choleskyStep A t).mulVecLin := by
  let M : Matrix n n K := fun j k => if k = t then A j t / A t t else 0
  have hfactor : choleskyStep A t = (1 - M) * A := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    ext j k
    simp only [choleskyStep_apply, Matrix.sub_apply, Matrix.mul_apply]
    simp only [M, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [div_eq_mul_inv]
    ring
  intro x hx
  change A *ᵥ x = 0 at hx
  change choleskyStep A t *ᵥ x = 0
  rw [hfactor, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- Every nonzero diagonal Cholesky pivot strictly reduces rank. Source: manuscript `sa:rp-rank`;
CETW (2025), exact-rank exhaustion. The proof adds the pivot coordinate to the kernel, so it does
not require a chosen basis of the residual range. -/
theorem rank_choleskyStep_lt {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) :
    (choleskyStep A t).rank < A.rank := by
  let e : n → K := Pi.single t 1
  have hAe : A *ᵥ e ≠ 0 := by
    intro h
    have he := congrFun h t
    apply ht
    simpa only [e, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply,
      Pi.zero_apply] using he
  have hSe : choleskyStep A t *ᵥ e = 0 := by
    dsimp only [e]
    rw [Matrix.mulVec_single_one]
    ext j
    exact choleskyStep_apply_pivot_right_of_ne_zero ht j
  have hker : LinearMap.ker A.mulVecLin < LinearMap.ker (choleskyStep A t).mulVecLin := by
    refine lt_of_le_of_ne (ker_mulVecLin_le_ker_choleskyStep A t) ?_
    intro heq
    have he : e ∈ LinearMap.ker (choleskyStep A t).mulVecLin := hSe
    rw [← heq] at he
    exact hAe he
  have hk := Submodule.finrank_lt_finrank_of_lt hker
  have hA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hS := LinearMap.finrank_range_add_finrank_ker (choleskyStep A t).mulVecLin
  change A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) = _ at hA
  change (choleskyStep A t).rank +
    Module.finrank K (LinearMap.ker (choleskyStep A t).mulVecLin) = _ at hS
  omega

end Field

section Real

variable {n : Type*} [Fintype n]

/-- The quadratic form of a Cholesky step: `xᵀ (A − A(:,t) A(t,:) / A(t,t)) x =
xᵀ A x − (xᵀ A(:,t)) (A(t,:) x) / A(t,t)`. -/
theorem dotProduct_choleskyStep_mulVec (A : Matrix n n ℝ) (t : n) (x : n → ℝ) :
    x ⬝ᵥ choleskyStep A t *ᵥ x =
      x ⬝ᵥ A *ᵥ x - (A t t)⁻¹ * ((∑ i, x i * A i t) * ∑ j, A t j * x j) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  simp only [dotProduct, mulVec, choleskyStep_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [DecidableEq n]

/-- One Cholesky step preserves positive semidefiniteness, for any pivot (for `A(t,t) = 0` the
step is the identity). Proof: `xᵀ (choleskyStep A t) x = zᵀ A z` at
`z = x − (A(t,:) x / A(t,t)) eₜ`. Golub–Van Loan 2013, §4.2.8; special case of Albert 1969,
Thm 1 (atlas `generalized-schur-complement-psd`); manuscript `sa:rp-one-step`. -/
theorem posSemidef_choleskyStep {A : Matrix n n ℝ} (hA : A.PosSemidef) (t : n) :
    (choleskyStep A t).PosSemidef := by
  have hsym : ∀ i j, A i j = A j i := fun i j => by
    have := congrFun (congrFun hA.isHermitian j) i
    simpa using this
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial, choleskyStep_apply]
    rw [hsym j i, hsym j t, hsym t i]; ring
  · set α := -((A t t)⁻¹ * ∑ j, A t j * x j) with hα
    have hx := (posSemidef_iff_dotProduct_mulVec.1 hA).2 (x + α • Pi.single t 1)
    have hexp : (x + α • Pi.single t 1) ⬝ᵥ A *ᵥ (x + α • Pi.single t 1) =
        x ⬝ᵥ A *ᵥ x + α * (∑ i, x i * A i t) + α * (∑ j, A t j * x j) + α ^ 2 * A t t := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      simp [dotProduct, mulVec, Pi.single_apply]
      ring
    have hs : ∑ i, x i * A i t = ∑ j, A t j * x j :=
      Finset.sum_congr rfl fun i _ => by rw [hsym i t, mul_comm]
    simp only [star_trivial] at hx ⊢
    rw [hexp, hs] at hx
    rw [dotProduct_choleskyStep_mulVec, hs]
    have key : α ^ 2 * A t t = (A t t)⁻¹ * ((∑ j, A t j * x j) * ∑ j, A t j * x j) := by
      rw [hα]
      by_cases ha : A t t = 0
      · simp [ha]
      · field_simp
    have key2 : α * ∑ j, A t j * x j = -((A t t)⁻¹ * ((∑ j, A t j * x j) * ∑ j, A t j * x j)) := by
      rw [hα]; ring
    linarith

omit [DecidableEq n] in
/-- A Cholesky step on a PSD matrix decreases it in Loewner order: `A − choleskyStep A t =
A(:,t) A(:,t)ᵀ / A(t,t)` is PSD. Source: manuscript `sa:rp-one-step`; CETW (2025), PSD order
invariant. -/
theorem posSemidef_sub_choleskyStep {A : Matrix n n ℝ} (hA : A.PosSemidef) (t : n) :
    (A - choleskyStep A t).PosSemidef := by
  have hc : (fun j => A t j) = star fun i => A i t := by
    funext j; exact (hA.isHermitian.apply t j).symm
  have he : A - choleskyStep A t =
      (A t t)⁻¹ • vecMulVec (fun i => A i t) (star fun i => A i t) := by
    rw [choleskyStep, ← hc]
    abel
  rw [he]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (inv_nonneg.mpr hA.diag_nonneg)

/-- After a Cholesky step on a PSD matrix the pivot row vanishes. -/
theorem choleskyStep_apply_pivot_left {A : Matrix n n ℝ} (hA : A.PosSemidef) (t j : n) :
    choleskyStep A t t j = 0 := by
  rw [choleskyStep_apply]
  by_cases h : A t t = 0
  · rw [apply_eq_zero_of_posSemidef_of_apply_self_eq_zero' hA h j]; simp
  · field_simp; ring

/-- After a Cholesky step on a PSD matrix the pivot column vanishes. -/
theorem choleskyStep_apply_pivot_right {A : Matrix n n ℝ} (hA : A.PosSemidef) (t i : n) :
    choleskyStep A t i t = 0 := by
  rw [choleskyStep_apply]
  by_cases h : A t t = 0
  · rw [apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA h i]; simp
  · field_simp; ring

end Real

end NLAlib
