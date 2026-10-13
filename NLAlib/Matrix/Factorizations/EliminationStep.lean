import Mathlib.Analysis.Matrix.Order
import NLAlib.Matrix.Basic.GramVanishing

/-!
# One step of (pivoted) elimination

`eliminationStep A t = A − A(:,t) A(t,:) / A(t,t)`, the square-root-free rank-one Schur update
on the pivot `t` (one step of Gaussian elimination, or of pivoted Cholesky without the square
root), total in the pivot: a zero pivot leaves `A` unchanged. Stated over any field; the positive
semidefinite API is over `[RCLike 𝕜]`.

* `eliminationStep_apply`: entries `aᵢⱼ − aᵢₜ aₜⱼ / aₜₜ`;
* `eliminationStep_apply_pivot_left/right_of_ne_zero`: a nonzero pivot zeroes its row and column;
* `ker_mulVecLin_le_ker_eliminationStep`, `rank_eliminationStep_lt`,
  `rank_eliminationStep_add_one_eq`: the kernel grows by the pivot line, the rank drops by one;
* `isHermitian_eliminationStep`, `posSemidef_eliminationStep`, `eliminationStep_le`: for PSD `A`
  the step is PSD and decreases `A` in Loewner order, for any pivot;
* `eliminationStep_apply_pivot_left/right`: on a PSD matrix every pivot zeroes its row and column.

The pivot-history recursion is `partialCholeskyResidual` (LowRank/Cholesky/PartialCholesky); the
step is one-column Nyström (`eliminationStep_eq_sub_nystrom`, LowRank/Cholesky/CholeskyPivot);
the pivot law of RPCholesky is `choleskyPivotProbability`
(`Matrix/Factorizations/CholeskyPivotProbability.lean`).
Golub–Van Loan 2013, §3.2.1 and §4.2.8–4.2.9; Chen–Epperly–Tropp–Webber 2023 (RPCholesky), §2.
Atlas: helper for `partial-cholesky-nystrom` and `rpcholesky`.
-/

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace NLAlib

section Field

variable {K : Type*} [Field K] {n : Type*}

/-- **One elimination step** on pivot `t`: `A − A(:,t) A(t,:) / A(t,t)`, the Schur complement of
`A(t,t)` padded with a zero row and column at `t`. Total: for `A(t,t) = 0` it returns `A`.
Golub–Van Loan 2013, §3.2.1, §4.2.9; CETW 2023, §2. -/
def eliminationStep (A : Matrix n n K) (t : n) : Matrix n n K :=
  A - (A t t)⁻¹ • vecMulVec (fun i => A i t) fun j => A t j

/-- Entrywise form of an elimination step: `aᵢⱼ − aᵢₜ aₜⱼ / aₜₜ`. -/
@[simp]
theorem eliminationStep_apply (A : Matrix n n K) (t i j : n) :
    eliminationStep A t i j = A i j - (A t t)⁻¹ * (A i t * A t j) := by
  simp [eliminationStep, vecMulVec_apply]

/-- The zero matrix is fixed by every elimination step. -/
@[simp] theorem eliminationStep_zero (t : n) : eliminationStep (0 : Matrix n n K) t = 0 := by
  ext i j
  simp

/-- A zero pivot leaves the matrix unchanged. -/
theorem eliminationStep_eq_self_of_apply_self_eq_zero {A : Matrix n n K} {t : n}
    (ht : A t t = 0) : eliminationStep A t = A := by
  simp [eliminationStep, ht]

/-- A nonzero pivot eliminates its entire row (no positivity needed). -/
theorem eliminationStep_apply_pivot_left_of_ne_zero {A : Matrix n n K} {t : n} (ht : A t t ≠ 0)
    (j : n) : eliminationStep A t t j = 0 := by
  rw [eliminationStep_apply, ← mul_assoc, inv_mul_cancel₀ ht, one_mul, sub_self]

/-- A nonzero pivot eliminates its entire column (no positivity needed). -/
theorem eliminationStep_apply_pivot_right_of_ne_zero {A : Matrix n n K} {t : n} (ht : A t t ≠ 0)
    (i : n) : eliminationStep A t i t = 0 := by
  rw [eliminationStep_apply, mul_comm (A i t), ← mul_assoc, inv_mul_cancel₀ ht, one_mul, sub_self]

/-- An elimination step keeps zero rows zero. -/
theorem eliminationStep_apply_eq_zero_of_row {A : Matrix n n K} {u : n} (hu : ∀ j, A u j = 0)
    (t j : n) : eliminationStep A t u j = 0 := by
  simp [hu]

/-- An elimination step keeps zero columns zero. -/
theorem eliminationStep_apply_eq_zero_of_col {A : Matrix n n K} {u : n} (hu : ∀ i, A i u = 0)
    (t i : n) : eliminationStep A t i u = 0 := by
  simp [hu]

variable [Fintype n] [DecidableEq n]

/-- The elimination step is the original matrix applied to the pivot-corrected vector:
`(eliminationStep A t) x = A (x − ((A x)ₜ / aₜₜ) eₜ)`. Golub–Van Loan 2013, §3.2.1. -/
theorem eliminationStep_mulVec_eq (A : Matrix n n K) (t : n) (x : n → K) :
    eliminationStep A t *ᵥ x = A *ᵥ (x - ((A *ᵥ x) t / A t t) • Pi.single t 1) := by
  rw [eliminationStep, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_smul, Matrix.col,
    Matrix.transpose_apply, Matrix.mulVec, div_eq_mul_inv]
  ring

/-- An elimination step can only enlarge the kernel: `eliminationStep A t = (1 − M) A` with
`M = A(:,t) eₜᵀ / A(t,t)`. CETW 2023, §2 (exhaustion of the column range). -/
theorem ker_mulVecLin_le_ker_eliminationStep (A : Matrix n n K) (t : n) :
    LinearMap.ker A.mulVecLin ≤ LinearMap.ker (eliminationStep A t).mulVecLin := by
  intro x hx
  change A *ᵥ x = 0 at hx
  change eliminationStep A t *ᵥ x = 0
  rw [eliminationStep_mulVec_eq, hx]
  simp [hx]

/-- A nonzero pivot adds exactly its coordinate line to the kernel. -/
theorem ker_eliminationStep_eq_sup_span_singleton {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) :
    LinearMap.ker (eliminationStep A t).mulVecLin =
      LinearMap.ker A.mulVecLin ⊔ Submodule.span K {Pi.single t (1 : K)} := by
  apply le_antisymm
  · intro x hx
    let a := (A *ᵥ x) t / A t t
    have hy : x - a • Pi.single t (1 : K) ∈ LinearMap.ker A.mulVecLin := by
      change A *ᵥ (x - a • Pi.single t (1 : K)) = 0
      rw [← eliminationStep_mulVec_eq]
      exact hx
    have he : a • Pi.single t (1 : K) ∈ Submodule.span K {Pi.single t (1 : K)} :=
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    exact Submodule.mem_sup.mpr ⟨_, hy, _, he, by abel⟩
  · apply sup_le (ker_mulVecLin_le_ker_eliminationStep A t)
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    change eliminationStep A t *ᵥ Pi.single t 1 = 0
    rw [Matrix.mulVec_single_one]
    ext j
    exact eliminationStep_apply_pivot_right_of_ne_zero ht j

/-- A nonzero pivot reduces the rank by exactly one. CETW 2023, §2. -/
theorem rank_eliminationStep_add_one_eq {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) :
    (eliminationStep A t).rank + 1 = A.rank := by
  have he : Pi.single t (1 : K) ∉ LinearMap.ker A.mulVecLin := by
    intro hz
    have hh := congrFun hz t
    apply ht
    simpa using hh
  have hker := Submodule.finrank_sup_span_singleton he
  rw [← ker_eliminationStep_eq_sup_span_singleton ht] at hker
  have hA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hS := LinearMap.finrank_range_add_finrank_ker (eliminationStep A t).mulVecLin
  change A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) = _ at hA
  change (eliminationStep A t).rank +
    Module.finrank K (LinearMap.ker (eliminationStep A t).mulVecLin) = _ at hS
  omega

/-- Every nonzero pivot strictly reduces the rank. CETW 2023, §2. -/
theorem rank_eliminationStep_lt {A : Matrix n n K} {t : n} (ht : A t t ≠ 0) :
    (eliminationStep A t).rank < A.rank := by
  have := rank_eliminationStep_add_one_eq ht
  omega

end Field

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The sesquilinear form of an elimination step: `x̄ᵀ (A − A(:,t) A(t,:) / A(t,t)) x =
x̄ᵀ A x − (x̄ᵀ A(:,t)) (A(t,:) x) / A(t,t)`. -/
theorem star_dotProduct_eliminationStep_mulVec (A : Matrix n n 𝕜) (t : n) (x : n → 𝕜) :
    star x ⬝ᵥ eliminationStep A t *ᵥ x =
      star x ⬝ᵥ A *ᵥ x - (A t t)⁻¹ * ((∑ i, star (x i) * A i t) * ∑ j, A t j * x j) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  simp only [dotProduct, mulVec, eliminationStep_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [Fintype n] in
/-- An elimination step of a Hermitian matrix is Hermitian. -/
theorem isHermitian_eliminationStep {A : Matrix n n 𝕜} (hA : A.IsHermitian) (t : n) :
    (eliminationStep A t).IsHermitian := by
  have hr : star (fun j => A t j) = fun i => A i t := by funext j; exact hA.apply j t
  have hc : star (fun i => A i t) = fun j => A t j := by funext j; exact hA.apply t j
  show (eliminationStep A t)ᴴ = eliminationStep A t
  simp only [eliminationStep, Matrix.conjTranspose_sub, hA.eq, Matrix.conjTranspose_smul,
    star_inv₀, hA.apply t t, Matrix.conjTranspose_vecMulVec, hr, hc]

variable [DecidableEq n]

/-- One elimination step preserves positive semidefiniteness, for any pivot (a zero pivot is
the identity step): `eliminationStep A t = Mᴴ A M` with `M = I − eₜ A(t,:) / A(t,t)`.
Golub–Van Loan 2013, §4.2.8; special case of Albert 1969, Thm 1
(atlas `generalized-schur-complement-psd`). -/
theorem posSemidef_eliminationStep {A : Matrix n n 𝕜} (hA : A.PosSemidef) (t : n) :
    (eliminationStep A t).PosSemidef := by
  by_cases ht : A t t = 0
  · rw [eliminationStep_eq_self_of_apply_self_eq_zero ht]
    exact hA
  let e : n → 𝕜 := Pi.single t 1
  let M : Matrix n n 𝕜 := 1 - (A t t)⁻¹ • Matrix.vecMulVec e (fun j => A t j)
  have hAM : A * M = eliminationStep A t := by
    change A * (1 - (A t t)⁻¹ • Matrix.vecMulVec e (fun j => A t j)) = _
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec]
    simp only [e, Matrix.mulVec_single_one, eliminationStep]
    rfl
  have hMA : Mᴴ * A = eliminationStep A t := by
    have h := congrArg Matrix.conjTranspose hAM
    simpa only [Matrix.conjTranspose_mul, hA.isHermitian.eq,
      (isHermitian_eliminationStep hA.isHermitian t).eq] using h
  have hSe : eliminationStep A t *ᵥ e = 0 := by
    dsimp only [e]
    rw [Matrix.mulVec_single_one]
    ext j
    exact eliminationStep_apply_pivot_right_of_ne_zero ht j
  have hSM : eliminationStep A t * M = eliminationStep A t := by
    change eliminationStep A t * (1 - (A t t)⁻¹ • Matrix.vecMulVec e (fun j => A t j)) = _
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec,
      hSe, Matrix.zero_vecMulVec, smul_zero, sub_zero]
  have hf : Mᴴ * A * M = eliminationStep A t := by rw [hMA, hSM]
  rw [← hf]
  exact hA.conjTranspose_mul_mul_same M

omit [DecidableEq n] in
/-- An elimination step on a PSD matrix decreases it in Loewner order:
`A − eliminationStep A t = A(:,t) A(:,t)ᴴ / A(t,t)` is PSD. Golub–Van Loan 2013, §4.2.8;
CETW 2023, §2. -/
theorem eliminationStep_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) (t : n) :
    eliminationStep A t ≤ A := by
  rw [Matrix.le_iff]
  have hc : (fun j => A t j) = star fun i => A i t := by
    funext j; exact (hA.isHermitian.apply t j).symm
  have hd : ((RCLike.re (A t t) : ℝ) : 𝕜) = A t t :=
    RCLike.conj_eq_iff_re.mp (hA.isHermitian.apply t t)
  have hd0 : 0 ≤ RCLike.re (A t t) := (RCLike.nonneg_iff.mp hA.diag_nonneg).1
  have hinv : 0 ≤ (A t t)⁻¹ := by
    rw [← hd, ← RCLike.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hd0)
  have he : A - eliminationStep A t =
      (A t t)⁻¹ • Matrix.vecMulVec (fun i => A i t) (star fun i => A i t) := by
    rw [eliminationStep, hc]
    abel
  rw [he]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul hinv

/-- After an elimination step on a PSD matrix the pivot row vanishes (also at a zero pivot,
whose row is already zero). -/
theorem eliminationStep_apply_pivot_left {A : Matrix n n 𝕜} (hA : A.PosSemidef) (t j : n) :
    eliminationStep A t t j = 0 := by
  by_cases h : A t t = 0
  · rw [eliminationStep_eq_self_of_apply_self_eq_zero h]
    exact apply_eq_zero_of_posSemidef_of_apply_self_eq_zero' hA h j
  · exact eliminationStep_apply_pivot_left_of_ne_zero h j

/-- After an elimination step on a PSD matrix the pivot column vanishes. -/
theorem eliminationStep_apply_pivot_right {A : Matrix n n 𝕜} (hA : A.PosSemidef) (t i : n) :
    eliminationStep A t i t = 0 := by
  by_cases h : A t t = 0
  · rw [eliminationStep_eq_self_of_apply_self_eq_zero h]
    exact apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA h i
  · exact eliminationStep_apply_pivot_right_of_ne_zero h i

end RCLike

end NLAlib
