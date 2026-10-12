import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual complex coordinate Cholesky pivots

The square-root-free rank-one Schur update preserves complex positive
semidefiniteness and decreases the residual in Loewner order. The finite
diagonal-over-real-trace pivot probabilities use the actual complex residual.
Source: CETW (2025), RPCholesky; manuscript `sa:rp-update` and audit Part VII.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual complex Cholesky coordinate residual step, with totalized zero
pivot behavior. Source: manuscript `sa:rp-update`; CETW (2025). -/
def complexCholeskyResidualStep (R : Matrix n n ℂ) (i : n) : Matrix n n ℂ :=
  R - (R i i)⁻¹ • Matrix.vecMulVec (R.col i) (R.row i)

omit [Fintype n] [DecidableEq n] in
/-- The complex residual step has the classical Schur-update entries.
Source: manuscript `sa:rp-update`; CETW (2025). -/
theorem complexCholeskyResidualStep_apply (R : Matrix n n ℂ) (i j k : n) :
    complexCholeskyResidualStep R i j k = R j k - R j i * (R i i)⁻¹ * R i k := by
  simp only [complexCholeskyResidualStep, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.col, Matrix.row, Matrix.transpose_apply, smul_eq_mul]
  ring

omit [Fintype n] [DecidableEq n] in
/-- Zero complex residuals are absorbing for every pivot index.
Source: manuscript `sa:rp-update`, absorbing convention. -/
@[simp] theorem complexCholeskyResidualStep_zero (i : n) :
    complexCholeskyResidualStep (0 : Matrix n n ℂ) i = 0 := by
  ext j k
  simp [complexCholeskyResidualStep_apply]

omit [Fintype n] [DecidableEq n] in
/-- A zero diagonal pivot leaves the complex residual unchanged.
Source: manuscript `sa:rp-update`, totalized zero-pivot convention. -/
theorem complexCholeskyResidualStep_eq_self_of_diag_eq_zero
    {R : Matrix n n ℂ} {i : n} (hi : R i i = 0) :
    complexCholeskyResidualStep R i = R := by
  simp only [complexCholeskyResidualStep, hi, inv_zero, zero_smul, sub_zero]

omit [Fintype n] [DecidableEq n] in
/-- A nonzero complex pivot eliminates its entire row.
Source: manuscript `sa:rp-rank`, rank-exhaustion argument. -/
theorem complexCholeskyResidualStep_row_eq_zero {R : Matrix n n ℂ} {i : n}
    (hi : R i i ≠ 0) (j : n) : complexCholeskyResidualStep R i i j = 0 := by
  rw [complexCholeskyResidualStep_apply, mul_inv_cancel₀ hi, one_mul, sub_self]

omit [Fintype n] [DecidableEq n] in
/-- A complex Hermitian coordinate update remains Hermitian.
Source: manuscript `sa:rp-update`, conjugate rank-one update. -/
theorem isHermitian_complexCholeskyResidualStep {R : Matrix n n ℂ}
    (hR : R.IsHermitian) (i : n) : (complexCholeskyResidualStep R i).IsHermitian := by
  have hr : star (R.row i) = R.col i := by funext j; exact hR.apply j i
  have hc : star (R.col i) = R.row i := by funext j; exact hR.apply i j
  show (complexCholeskyResidualStep R i)ᴴ = complexCholeskyResidualStep R i
  simp only [complexCholeskyResidualStep, Matrix.conjTranspose_sub, hR.eq,
    Matrix.conjTranspose_smul, star_inv₀, hR.apply i i,
    Matrix.conjTranspose_vecMulVec, hr, hc]

/-- Every actual complex coordinate pivot preserves positive semidefiniteness.
The proof is a square-root-free congruence, valid also at zero pivots.
Source: manuscript `sa:rp-one-step`; audit Part VII, completion of squares. -/
theorem posSemidef_complexCholeskyResidualStep {R : Matrix n n ℂ}
    (hR : R.PosSemidef) (i : n) : (complexCholeskyResidualStep R i).PosSemidef := by
  by_cases hi : R i i = 0
  · rw [complexCholeskyResidualStep_eq_self_of_diag_eq_zero hi]
    exact hR
  let e : n → ℂ := Pi.single i 1
  let M : Matrix n n ℂ := 1 - (R i i)⁻¹ • Matrix.vecMulVec e (R.row i)
  have hRM : R * M = complexCholeskyResidualStep R i := by
    change R * (1 - (R i i)⁻¹ • Matrix.vecMulVec e (R.row i)) = _
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec]
    simp only [e, Matrix.mulVec_single_one, complexCholeskyResidualStep]
  have hMR : Mᴴ * R = complexCholeskyResidualStep R i := by
    have h := congrArg Matrix.conjTranspose hRM
    simpa only [Matrix.conjTranspose_mul, hR.isHermitian.eq,
      (isHermitian_complexCholeskyResidualStep hR.isHermitian i).eq] using h
  have hSe : complexCholeskyResidualStep R i *ᵥ e = 0 := by
    dsimp only [e]
    rw [Matrix.mulVec_single_one]
    ext j
    change complexCholeskyResidualStep R i j i = 0
    rw [complexCholeskyResidualStep_apply, mul_assoc, inv_mul_cancel₀ hi, mul_one, sub_self]
  have hSM : complexCholeskyResidualStep R i * M = complexCholeskyResidualStep R i := by
    change complexCholeskyResidualStep R i *
      (1 - (R i i)⁻¹ • Matrix.vecMulVec e (R.row i)) = _
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec,
      hSe, Matrix.zero_vecMulVec, smul_zero, sub_zero]
  have hf : Mᴴ * R * M = complexCholeskyResidualStep R i := by rw [hMR, hSM]
  rw [← hf]
  exact hR.conjTranspose_mul_mul_same M

omit [DecidableEq n] in
/-- The actual complex coordinate residual decreases in Loewner order.
Source: manuscript `sa:rp-one-step`; audit Part VII, positive rank-one correction. -/
theorem posSemidef_sub_complexCholeskyResidualStep {R : Matrix n n ℂ}
    (hR : R.PosSemidef) (i : n) : (R - complexCholeskyResidualStep R i).PosSemidef := by
  have hc : R.row i = star (R.col i) := by funext j; exact (hR.isHermitian.apply i j).symm
  have hd : ((R i i).re : ℂ) = R i i :=
    Complex.conj_eq_iff_re.mp (hR.isHermitian.apply i i)
  have hd0 : 0 ≤ (R i i).re := (RCLike.nonneg_iff.mp hR.diag_nonneg).1
  have hinv : 0 ≤ (R i i)⁻¹ := by
    rw [← hd, ← Complex.ofReal_inv]
    exact RCLike.nonneg_iff.mpr ⟨inv_nonneg.mpr hd0, by simp⟩
  have he : R - complexCholeskyResidualStep R i =
      (R i i)⁻¹ • Matrix.vecMulVec (R.col i) (star (R.col i)) := by
    rw [complexCholeskyResidualStep, hc]
    abel
  rw [he]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul hinv

/-- Every complex coordinate step contains the original kernel.
Source: manuscript `sa:rp-rank`, factorization through the original operator. -/
theorem ker_mulVecLin_le_ker_complexCholeskyResidualStep (R : Matrix n n ℂ) (i : n) :
    LinearMap.ker R.mulVecLin ≤ LinearMap.ker (complexCholeskyResidualStep R i).mulVecLin := by
  let M : Matrix n n ℂ := fun j k => if k = i then R j i / R i i else 0
  have hfactor : complexCholeskyResidualStep R i = (1 - M) * R := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    ext j k
    simp only [complexCholeskyResidualStep_apply, Matrix.sub_apply, Matrix.mul_apply]
    simp only [M, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [div_eq_mul_inv]
  intro x hx
  change R *ᵥ x = 0 at hx
  change complexCholeskyResidualStep R i *ᵥ x = 0
  rw [hfactor, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- Every nonzero complex diagonal pivot strictly decreases the native complex
rank. Source: manuscript `sa:rp-rank`; CETW (2025). -/
theorem rank_complexCholeskyResidualStep_lt {R : Matrix n n ℂ} {i : n}
    (hi : R i i ≠ 0) : (complexCholeskyResidualStep R i).rank < R.rank := by
  let e : n → ℂ := Pi.single i 1
  have hRe : R *ᵥ e ≠ 0 := by
    intro h
    have he := congrFun h i
    apply hi
    simpa only [e, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply,
      Pi.zero_apply] using he
  have hSe : complexCholeskyResidualStep R i *ᵥ e = 0 := by
    dsimp only [e]
    rw [Matrix.mulVec_single_one]
    ext j
    change complexCholeskyResidualStep R i j i = 0
    rw [complexCholeskyResidualStep_apply, mul_assoc, inv_mul_cancel₀ hi, mul_one, sub_self]
  have hker : LinearMap.ker R.mulVecLin <
      LinearMap.ker (complexCholeskyResidualStep R i).mulVecLin := by
    refine lt_of_le_of_ne (ker_mulVecLin_le_ker_complexCholeskyResidualStep R i) ?_
    intro heq
    have he : e ∈ LinearMap.ker (complexCholeskyResidualStep R i).mulVecLin := hSe
    rw [← heq] at he
    exact hRe he
  have hk := Submodule.finrank_lt_finrank_of_lt hker
  have hR := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
  have hS := LinearMap.finrank_range_add_finrank_ker (complexCholeskyResidualStep R i).mulVecLin
  change R.rank + Module.finrank ℂ (LinearMap.ker R.mulVecLin) = _ at hR
  change (complexCholeskyResidualStep R i).rank +
    Module.finrank ℂ (LinearMap.ker (complexCholeskyResidualStep R i).mulVecLin) = _ at hS
  omega

/-- The complex Schur step equals the original operator applied to the pivot-corrected
vector. Source: audit Part VII, square-root-free kernel calculation. -/
theorem complexCholeskyResidualStep_mulVec_eq
    (R : Matrix n n ℂ) (i : n) (x : n → ℂ) :
    complexCholeskyResidualStep R i *ᵥ x =
      R *ᵥ (x - ((R *ᵥ x) i / R i i) • Pi.single i 1) := by
  rw [complexCholeskyResidualStep, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_single_one]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_smul,
    Matrix.row, Matrix.col, Matrix.transpose_apply, Matrix.mulVec, div_eq_mul_inv]
  ring

/-- A nonzero complex pivot adds exactly its coordinate line to the kernel.
Source: audit Part VII, algebraic direct-sum kernel identity. -/
theorem ker_complexCholeskyResidualStep_eq_sup_span_singleton
    {R : Matrix n n ℂ} {i : n} (hi : R i i ≠ 0) :
    LinearMap.ker (complexCholeskyResidualStep R i).mulVecLin =
      LinearMap.ker R.mulVecLin ⊔ Submodule.span ℂ {Pi.single i (1 : ℂ)} := by
  apply le_antisymm
  · intro x hx
    let a := (R *ᵥ x) i / R i i
    have hy : x - a • Pi.single i (1 : ℂ) ∈ LinearMap.ker R.mulVecLin := by
      change R *ᵥ (x - a • Pi.single i (1 : ℂ)) = 0
      rw [← complexCholeskyResidualStep_mulVec_eq]
      exact hx
    have he : a • Pi.single i (1 : ℂ) ∈ Submodule.span ℂ {Pi.single i (1 : ℂ)} :=
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    exact Submodule.mem_sup.mpr ⟨_, hy, _, he, by abel⟩
  · apply sup_le (ker_mulVecLin_le_ker_complexCholeskyResidualStep R i)
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    change complexCholeskyResidualStep R i *ᵥ Pi.single i 1 = 0
    rw [Matrix.mulVec_single_one]
    ext j
    change complexCholeskyResidualStep R i j i = 0
    rw [complexCholeskyResidualStep_apply, mul_assoc, inv_mul_cancel₀ hi, mul_one, sub_self]

/-- A nonzero complex pivot reduces the native complex rank by exactly one.
Source: audit Part VII, algebraic kernel sum and rank-nullity. -/
theorem rank_complexCholeskyResidualStep_add_one_eq
    {R : Matrix n n ℂ} {i : n} (hi : R i i ≠ 0) :
    (complexCholeskyResidualStep R i).rank + 1 = R.rank := by
  have he : Pi.single i (1 : ℂ) ∉ LinearMap.ker R.mulVecLin := by
    intro hz
    have hh := congrFun hz i
    apply hi
    simpa using hh
  have hker := Submodule.finrank_sup_span_singleton he
  rw [← ker_complexCholeskyResidualStep_eq_sup_span_singleton hi] at hker
  have hR := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
  have hS := LinearMap.finrank_range_add_finrank_ker (complexCholeskyResidualStep R i).mulVecLin
  change R.rank + Module.finrank ℂ (LinearMap.ker R.mulVecLin) = _ at hR
  change (complexCholeskyResidualStep R i).rank +
    Module.finrank ℂ (LinearMap.ker (complexCholeskyResidualStep R i).mulVecLin) = _ at hS
  omega

omit [Fintype n] [DecidableEq n] in
/-- A complex PSD diagonal entry is exactly its embedded nonnegative real part.
Source: Hermitian positivity; manuscript `sa:rp-update`, pivot probabilities. -/
theorem diag_eq_ofReal_re_of_complex_posSemidef {R : Matrix n n ℂ}
    (hR : R.PosSemidef) (i : n) : R i i = ((R i i).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (hR.isHermitian.apply i i)).symm

omit [DecidableEq n] in
/-- The ordered complex PSD trace is its real complex trace, with no dimension
doubling. Source: audit Part VII, complex RPCholesky normalization. -/
theorem trace_eq_ofReal_re_of_complex_posSemidef {R : Matrix n n ℂ}
    (hR : R.PosSemidef) : R.trace = (R.trace.re : ℂ) := by
  have hi := (RCLike.nonneg_iff.mp hR.trace_nonneg).2
  change R.trace.im = 0 at hi
  apply Complex.ext <;> simp [hi]

omit [DecidableEq n] in
/-- A PSD matrix has nonnegative real complex trace.
Source: manuscript `sa:rp-one-step`; audit Part VII. -/
theorem re_trace_nonneg_of_complex_posSemidef {R : Matrix n n ℂ}
    (hR : R.PosSemidef) : 0 ≤ R.trace.re := (RCLike.nonneg_iff.mp hR.trace_nonneg).1

omit [DecidableEq n] in
/-- Zero real complex trace characterizes the zero PSD matrix.
Source: manuscript `sa:rp-one-step`, absorbing residual. -/
theorem re_trace_eq_zero_iff_of_complex_posSemidef {R : Matrix n n ℂ}
    (hR : R.PosSemidef) : R.trace.re = 0 ↔ R = 0 := by
  constructor
  · intro ht
    apply hR.trace_eq_zero_iff.mp
    rw [trace_eq_ofReal_re_of_complex_posSemidef hR, ht, Complex.ofReal_zero]
  · rintro rfl
    simp

/-- A zero PSD complex diagonal forces its actual complex column to vanish.
Source: manuscript `sa:rp-one-step`, zero selection probability. -/
theorem apply_eq_zero_of_complex_posSemidef_of_diag_eq_zero
    {R : Matrix n n ℂ} (hR : R.PosSemidef) {i : n} (hi : R i i = 0) (j : n) : R j i = 0 := by
  let e : n → ℂ := Pi.single i 1
  have hq : star e ⬝ᵥ (R *ᵥ e) = 0 := by simp [e, hi]
  have hz : R *ᵥ e = 0 := (hR.dotProduct_mulVec_zero_iff e).mp hq
  have hj := congrFun hz j
  simpa [e] using hj

/-- Complex diagonal-over-real-trace pivot probabilities, with a uniform
absorbing-state convention. Source: manuscript `sa:rp-update`; CETW (2025). -/
def complexCholeskyPivotProbability (R : Matrix n n ℂ) (i : n) : ℝ :=
  if R.trace.re = 0 then 1 / (Fintype.card n : ℝ) else (R i i).re / R.trace.re

omit [DecidableEq n] in
/-- The actual complex pivot probabilities sum to one.
Source: manuscript `sa:rp-update`, finite transition normalization. -/
theorem sum_complexCholeskyPivotProbability [Nonempty n] (R : Matrix n n ℂ) :
    ∑ i, complexCholeskyPivotProbability R i = 1 := by
  by_cases ht : R.trace.re = 0
  · simp only [complexCholeskyPivotProbability, if_pos ht, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero)
  · simp only [complexCholeskyPivotProbability, if_neg ht, ← Finset.sum_div]
    rw [show (∑ i, (R i i).re) = R.trace.re by simp [Matrix.trace, Complex.re_sum]]
    exact div_self ht

omit [DecidableEq n] in
/-- PSD complex residuals give nonnegative transition probabilities.
Source: manuscript `sa:rp-update`; CETW (2025). -/
theorem complexCholeskyPivotProbability_nonneg {R : Matrix n n ℂ}
    (hR : R.PosSemidef) (i : n) : 0 ≤ complexCholeskyPivotProbability R i := by
  unfold complexCholeskyPivotProbability
  split_ifs
  · positivity
  · exact div_nonneg (RCLike.nonneg_iff.mp hR.diag_nonneg).1
      (re_trace_nonneg_of_complex_posSemidef hR)

/-- The actual complex one-step mean is `R - R²/re(tr R)`.
Source: manuscript `sa:rp-one-step`; audit Part VII. -/
theorem sum_complexCholeskyPivotProbability_smul_step_eq [Nonempty n]
    {R : Matrix n n ℂ} (hR : R.PosSemidef) (ht : R.trace.re ≠ 0) :
    (∑ i, complexCholeskyPivotProbability R i • complexCholeskyResidualStep R i) =
      R - (R.trace.re)⁻¹ • (R * R) := by
  have hc : ∀ i j k, ((R i i).re / R.trace.re) •
      (R j i * (R i i)⁻¹ * R i k) = (R.trace.re)⁻¹ • (R j i * R i k) := by
    intro i j k
    by_cases hi : R i i = 0
    · rw [hi, apply_eq_zero_of_complex_posSemidef_of_diag_eq_zero hR hi j]
      simp
    · rw [Complex.real_smul, Complex.real_smul]
      rw [Complex.ofReal_div, Complex.ofReal_inv,
        ← diag_eq_ofReal_re_of_complex_posSemidef hR i]
      field_simp
  ext j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, complexCholeskyResidualStep_apply,
    smul_sub, Finset.sum_sub_distrib, Matrix.sub_apply]
  have hp : ∑ i, complexCholeskyPivotProbability R i • R j k = R j k := by
    rw [← Finset.sum_smul, sum_complexCholeskyPivotProbability, one_smul]
  rw [hp]
  simp only [complexCholeskyPivotProbability, if_neg ht, hc, ← Finset.smul_sum,
    Matrix.mul_apply]

/-- The actual complex trace mean includes its absorbing zero state.
Source: manuscript `sa:rp-one-step` and `sa:rp-recursion`; audit Part VII. -/
theorem sum_complexCholeskyPivotProbability_mul_re_trace_step_eq [Nonempty n]
    {R : Matrix n n ℂ} (hR : R.PosSemidef) :
    (∑ i, complexCholeskyPivotProbability R i * (complexCholeskyResidualStep R i).trace.re) =
      R.trace.re - (R * R).trace.re / R.trace.re := by
  by_cases ht : R.trace.re = 0
  · have hz : R = 0 := (re_trace_eq_zero_iff_of_complex_posSemidef hR).mp ht
    rw [hz]
    simp
  · have h := congrArg (fun M : Matrix n n ℂ => M.trace.re)
      (sum_complexCholeskyPivotProbability_smul_step_eq hR ht)
    simpa only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_sub, Complex.sub_re,
      Complex.re_sum, Complex.smul_re, smul_eq_mul, div_eq_mul_inv,
      mul_comm] using h

omit [DecidableEq n] in
/-- Native complex rank zero means the actual complex matrix is zero.
Source: rank--range identity; manuscript `sa:rp-rank`, exact termination. -/
theorem eq_zero_of_complex_matrix_rank_eq_zero {m : Type*} [Fintype m]
    {R : Matrix m n ℂ} (hR : R.rank = 0) : R = 0 := by
  have hrange : LinearMap.range R.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hR
  ext i j
  have hj : R.col j ∈ LinearMap.range R.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  rw [hrange, Submodule.mem_bot] at hj
  exact congrFun hj i

end NLAlib
