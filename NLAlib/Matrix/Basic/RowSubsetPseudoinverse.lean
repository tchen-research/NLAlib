import NLAlib.Matrix.Basic.RowSubsetAdjugate
import NLAlib.Matrix.Basic.GramAdjugate
import NLAlib.Matrix.Basic.MoorePenroseTransformations
import NLAlib.ForMathlib.Analysis.Matrix.DeterminantDerivative

/-!
# Determinant-weighted padded row pseudoinverses

Differentiate the all-data cross-Gram normalizer in its right argument. This gives
the complex trace pairing directly, using a real parameter and Jacobi's formula.
The Gram-adjugate cancellation makes the resulting Moore–Penrose identity valid
also at singular subsets. Division by the sampling normalizer belongs to the
probabilistic consumer.

Source: Dereziński–Warmuth 2018, Theorem 5 and Appendix B.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
private local instance : NormedSpace ℝ (Matrix d d 𝕜) where
  toModule := inferInstance
  norm_smul_le := by
    intro t A
    have he : t • A = (t : 𝕜) • A := by
      ext i j
      simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rw [he]
    simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul_le (t : 𝕜) A

/-- The actual Moore–Penrose inverse of the padded selected-row matrix. It retains
the original ambient row labels and is defined on singular subsets too. -/
def rowSubsetPseudoinverse (X : Matrix n d 𝕜) (S : Finset n) : Matrix d n 𝕜 :=
  moorePenroseInverse (coordinateSelector S * X)

omit [DecidableEq d] in
/-- Selecting all rows gives the original Moore–Penrose inverse. -/
@[simp] theorem rowSubsetPseudoinverse_univ (X : Matrix n d 𝕜) :
    rowSubsetPseudoinverse X Finset.univ = moorePenroseInverse X := by
  simp only [rowSubsetPseudoinverse, coordinateSelector_univ, Matrix.one_mul]

/-- Every supported full-column-rank restriction exactly recovers the original
column coordinates, even though the pseudoinverse retains padded row labels.
atlas: row-volume-pseudoinverse-unbiased (partial) -/
theorem rowSubsetPseudoinverse_mul_eq_one (X : Matrix n d 𝕜) (S : Finset n)
    (hS : IsUnit (rowSubsetGram X S)) : rowSubsetPseudoinverse X S * X = 1 := by
  have hG : IsUnit ((coordinateSelector S * X)ᴴ * (coordinateSelector S * X)) := by
    rwa [← rowSubsetGram_eq_conjTranspose_mul_self X S]
  rw [rowSubsetPseudoinverse, moorePenroseInverse_eq_pinvL _ hG, pinvL,
    ← rowSubsetGram_eq_conjTranspose_mul_self X S, Matrix.conjTranspose_mul,
    (coordinateSelector_isHermitian S).eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Xᴴ (coordinateSelector S) X]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)

/-- On a supported full-column-rank restriction, the padded pseudoinverse
row Gram is exactly the inverse selected column Gram. -/
theorem rowSubsetPseudoinverse_mul_conjTranspose_of_isUnit (X : Matrix n d 𝕜) (S : Finset n)
    (hS : IsUnit (rowSubsetGram X S)) :
    rowSubsetPseudoinverse X S * (rowSubsetPseudoinverse X S)ᴴ = (rowSubsetGram X S)⁻¹ := by
  calc
    _ = moorePenroseInverse ((coordinateSelector S * X)ᴴ * (coordinateSelector S * X)) :=
      (moorePenroseInverse_conjTranspose_mul_self _).symm
    _ = moorePenroseInverse (rowSubsetGram X S) :=
      congrArg moorePenroseInverse (rowSubsetGram_eq_conjTranspose_mul_self X S).symm
    _ = _ := moorePenroseInverse_eq_inv_of_isUnit _ hS

/-- Weighted padded pseudoinverse Grams equal weighted ordinary Gram inverses
on every subset. Singular zero-mass subsets are retained on both sides. -/
theorem rowSubsetVolume_smul_pseudoinverse_mul_conjTranspose (X : Matrix n d 𝕜) (S : Finset n) :
    rowSubsetVolume X S • (rowSubsetPseudoinverse X S * (rowSubsetPseudoinverse X S)ᴴ) =
      rowSubsetVolume X S • (rowSubsetGram X S)⁻¹ := by
  by_cases hzero : rowSubsetVolume X S = 0
  · rw [hzero, zero_smul, zero_smul]
  · rw [rowSubsetPseudoinverse_mul_conjTranspose_of_isUnit X S
      ((rowSubsetVolume_pos_iff_isUnit X S).mp
        (lt_of_le_of_ne (rowSubsetVolume_nonneg X S) (Ne.symm hzero)))]

/-- The exact inverse numerator is the adjugate with the singular-adjugate
term subtracted, at every subset and every rank. -/
theorem rowSubsetVolume_smul_inv_eq_adjugate_sub_ite (X : Matrix n d 𝕜) (S : Finset n) :
    rowSubsetVolume X S • (rowSubsetGram X S)⁻¹ =
      (rowSubsetGram X S).adjugate -
        if rowSubsetVolume X S = 0 then (rowSubsetGram X S).adjugate else 0 := by
  have hzero : (rowSubsetGram X S).det = 0 ↔ rowSubsetVolume X S = 0 := by
    rw [← ofReal_rowSubsetVolume]
    exact RCLike.ofReal_eq_zero
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), ofReal_rowSubsetVolume,
    det_smul_inv_eq_adjugate_sub_ite]
  simp only [hzero]

/-- The adjugate numerator equals the actual determinant-weighted padded
pseudoinverse at every subset, including its zero-mass singular cases. -/
theorem adjugate_rowSubsetGram_mul_conjTranspose_selector (X : Matrix n d 𝕜) (S : Finset n) :
    (rowSubsetGram X S).adjugate * Xᴴ * coordinateSelector S =
      rowSubsetVolume X S • rowSubsetPseudoinverse X S := by
  have h := adjugate_gram_mul_conjTranspose_eq_det_smul_moorePenroseInverse (coordinateSelector S * X)
  rw [← rowSubsetGram_eq_conjTranspose_mul_self X S, Matrix.conjTranspose_mul,
    (coordinateSelector_isHermitian S).eq, ← Matrix.mul_assoc] at h
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), ofReal_rowSubsetVolume]
  exact h

open scoped Matrix.Norms.L2Operator in
private theorem hasDerivAt_det_rowSubsetCrossGram_right
    (X H : Matrix n d 𝕜) (S : Finset n) :
    HasDerivAt (fun t : ℝ => (rowSubsetCrossGram X (X + t • H) S).det)
      ((rowSubsetGram X S).adjugate * rowSubsetCrossGram X H S).trace 0 := by
  have he : (fun t : ℝ => rowSubsetCrossGram X (X + t • H) S) =
      fun t => rowSubsetGram X S + t • rowSubsetCrossGram X H S := by
    funext t
    simp only [rowSubsetCrossGram, rowSubsetGram, Matrix.mul_add, Matrix.mul_smul]
  have hd : HasDerivAt (fun t : ℝ => rowSubsetCrossGram X (X + t • H) S)
      (rowSubsetCrossGram X H S) 0 := by
    rw [he]
    convert! (hasDerivAt_const (0 : ℝ) (rowSubsetGram X S)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (rowSubsetCrossGram X H S)) using 1
    simp only [zero_add, one_smul]
  simpa only [rowSubsetCrossGram, rowSubsetGram, zero_smul, add_zero] using hd.matrix_det

open scoped Matrix.Norms.L2Operator in
/-- Differentiating the cross-Gram normalizer gives the full adjugate numerator
identity over real or complex scalars. No rank or general-position assumption is
needed, and an arbitrary ambient row set may be used. -/
theorem sum_adjugate_rowSubsetGram_mul_conjTranspose_selector
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hds : Fintype.card d ≤ s) :
    (∑ S ∈ T.powersetCard s, (rowSubsetGram X S).adjugate * Xᴴ * coordinateSelector S) =
      ((T.card - Fintype.card d).choose (s - Fintype.card d) : 𝕜) •
        ((rowSubsetGram X T).adjugate * Xᴴ * coordinateSelector T) := by
  classical
  let c := (T.card - Fintype.card d).choose (s - Fintype.card d)
  let K := (∑ S ∈ T.powersetCard s, (rowSubsetGram X S).adjugate * Xᴴ * coordinateSelector S) -
    (c : 𝕜) • ((rowSubsetGram X T).adjugate * Xᴴ * coordinateSelector T)
  have hpair (H : Matrix n d 𝕜) : (K * H).trace = 0 := by
    have hl := HasDerivAt.fun_sum (fun S (_ : S ∈ T.powersetCard s) =>
      hasDerivAt_det_rowSubsetCrossGram_right X H S)
    have he : (fun t : ℝ => ∑ S ∈ T.powersetCard s,
        (rowSubsetCrossGram X (X + t • H) S).det) =
        fun t => (c : 𝕜) * (rowSubsetCrossGram X (X + t • H) T).det := by
      funext t
      exact sum_det_rowSubsetCrossGram_powersetCard X (X + t • H) T s hds
    rw [he] at hl
    have hh := hl.unique ((hasDerivAt_det_rowSubsetCrossGram_right X H T).const_mul (c : 𝕜))
    change (((∑ S ∈ T.powersetCard s, (rowSubsetGram X S).adjugate * Xᴴ * coordinateSelector S) -
      (c : 𝕜) • ((rowSubsetGram X T).adjugate * Xᴴ * coordinateSelector T)) * H).trace = 0
    simp only [Matrix.sub_mul, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    apply sub_eq_zero.mpr
    simpa only [rowSubsetCrossGram, Matrix.mul_assoc] using hh
  have hz : K = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (hpair Kᴴ)
  exact sub_eq_zero.mp hz

/-- The exact unnormalized Moore–Penrose expectation identity before division by
the positive row-volume mass. Singular subsets are included with their actual zero
weights. The ambient restriction may itself be deficient. -/
theorem sum_rowSubsetVolume_smul_pseudoinverse_powersetCard
    (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ) (hds : Fintype.card d ≤ s) :
    (∑ S ∈ T.powersetCard s, rowSubsetVolume X S • rowSubsetPseudoinverse X S) =
      (((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T) •
        rowSubsetPseudoinverse X T := by
  calc
    _ = ∑ S ∈ T.powersetCard s, (rowSubsetGram X S).adjugate * Xᴴ * coordinateSelector S := by
      apply Finset.sum_congr rfl
      intro S _
      exact (adjugate_rowSubsetGram_mul_conjTranspose_selector X S).symm
    _ = ((T.card - Fintype.card d).choose (s - Fintype.card d) : 𝕜) •
        ((rowSubsetGram X T).adjugate * Xᴴ * coordinateSelector T) :=
      sum_adjugate_rowSubsetGram_mul_conjTranspose_selector X T s hds
    _ = ((T.card - Fintype.card d).choose (s - Fintype.card d) : 𝕜) •
        (rowSubsetVolume X T • rowSubsetPseudoinverse X T) :=
      congrArg _ (adjugate_rowSubsetGram_mul_conjTranspose_selector X T)
    _ = _ := by rw [Nat.cast_smul_eq_nsmul 𝕜, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

end NLAlib
