/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Sketching.Sampling.ProjectionVolumeResidual
import NLAlib.Matrix.Basic.QuadForm
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Row-volume least-squares regression

An invertible change of column coordinates preserves both normalized row-volume sampling
and its fitted values on the support. The sharp projection-volume interpolation theorem
therefore applies to arbitrary full-column-rank real or complex designs. Singular subsets
have zero mass, and equality in the residual moment requires full support at the sampled size.

Source: Dereziński–Warmuth 2018, Theorem 8, with the necessary general-position condition
for equality. The Cramer and Cauchy–Binet proof is reused from
`NLAlib.Sketching.Sampling.ProjectionVolumeResidual`.
Atlas: `row-volume-regression-error`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {𝕜 n d r : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq n] in
private theorem exists_orthonormal_mul_isUnit_of_isUnit_gram (X : Matrix n d 𝕜)
    (hX : IsUnit (Xᴴ * X)) :
    ∃ (Q : Matrix n d 𝕜) (R : Matrix d d 𝕜), HasOrthonormalCols Q ∧ IsUnit R ∧ Q * R = X := by
  let R := CFC.sqrt (Xᴴ * X)
  have hG := (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  have hR : IsUnit R := (CFC.isUnit_sqrt_iff _ hG).2 hX
  have hRd := (Matrix.isUnit_iff_isUnit_det R).1 hR
  have hRR : R * R = Xᴴ * X := CFC.sqrt_mul_sqrt_self _ hG
  have hRh : Rᴴ = R := by
    simpa only [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg (Xᴴ * X)).star_eq
  refine ⟨X * R⁻¹, R, ?_, hR, Matrix.nonsing_inv_mul_cancel_right R X hRd⟩
  change (X * R⁻¹)ᴴ * (X * R⁻¹) = 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hRh]
  calc
    R⁻¹ * Xᴴ * (X * R⁻¹) = R⁻¹ * (Xᴴ * X) * R⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (R⁻¹ * R) * (R * R⁻¹) := by rw [← hRR]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hRd, Matrix.mul_nonsing_inv _ hRd, Matrix.one_mul]

private theorem rowSubsetVolume_mul_right (Q : Matrix n d 𝕜) (R : Matrix d d 𝕜)
    (S : Finset n) :
    rowSubsetVolume (Q * R) S = ‖R.det‖ ^ 2 * rowSubsetVolume Q S := by
  have hGram : rowSubsetGram (Q * R) S = Rᴴ * rowSubsetGram Q S * R := by
    simp only [rowSubsetGram, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [rowSubsetVolume, hGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    ← ofReal_rowSubsetVolume Q S]
  have he : star R.det * (rowSubsetVolume Q S : 𝕜) * R.det =
      ((‖R.det‖ ^ 2 * rowSubsetVolume Q S : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_mul, RCLike.ofReal_pow, RCLike.star_def]
    calc
      _ = (starRingEnd 𝕜 R.det * R.det) * (rowSubsetVolume Q S : 𝕜) := by ring
      _ = _ := by rw [RCLike.conj_mul]
  rw [he, RCLike.ofReal_re]

private theorem rowVolumeLaw_eq_projectionRowVolumeLaw (Q : Matrix n d 𝕜)
    (hQ : HasOrthonormalCols Q) (R : Matrix d d 𝕜) (hR : IsUnit R)
    (hT : 0 < rowSubsetVolume (Q * R) Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) :
    rowVolumeLaw (Q * R) Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard) =
      projectionRowVolumeLaw Q hQ := by
  apply Measure.ext_of_measureReal_singleton
  intro S
  rw [rowVolumeLaw_singleton, projectionRowVolumeLaw_singleton]
  have hRdet : R.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hc : ‖R.det‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hRdet)
  simp only [rowSubsetVolume_mul_right, rowSubsetVolume_univ_of_orthonormal Q hQ,
    Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one, rowVolumeWeight]
  by_cases hS : S.card = Fintype.card d
  · simp only [Finset.mem_powersetCard, Finset.subset_univ, hS, and_self, if_true]
    exact mul_div_cancel_left₀ _ hc
  · simp [hS]

private theorem mul_rowSubsetPseudoinverse_sizedSubset_mul_eq [Fintype r]
    (Q : Matrix n d 𝕜) (R : Matrix d d 𝕜) (hR : IsUnit R)
    (J : SizedSubset n d) (hJ : 0 < rowSubsetVolume Q J.val) (Y : Matrix n r 𝕜) :
    (Q * R) * (rowSubsetPseudoinverse (Q * R) J.val * Y) =
      projectionVolumeInterpolant Q Y J.val := by
  have hRdet : R.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hJ' : 0 < rowSubsetVolume (Q * R) J.val := by
    rw [rowSubsetVolume_mul_right]
    exact mul_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hRdet)) hJ
  rw [rowSubsetPseudoinverse_sizedSubset_mul _ J hJ' Y,
    projectionVolumeInterpolant, rowSubsetPseudoinverse_sizedSubset_mul _ J hJ Y]
  have hsub : (Q * R).submatrix (sizedSubsetIndex J) id =
      Q.submatrix (sizedSubsetIndex J) id * R := rfl
  rw [hsub, Matrix.mul_inv_rev]
  calc
    _ = Q * (R * R⁻¹) * ((Q.submatrix (sizedSubsetIndex J) id)⁻¹ *
        Y.submatrix (sizedSubsetIndex J) id) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det R).mp hR),
      Matrix.mul_one]

omit [DecidableEq n] in
private theorem mul_moorePenroseInverse_mul_right_eq (Q : Matrix n d 𝕜)
    (hQ : HasOrthonormalCols Q) (R : Matrix d d 𝕜) (hR : IsUnit R) :
    (Q * R) * moorePenroseInverse (Q * R) = Q * Qᴴ := by
  rw [moorePenroseInverse_mul_left_of_hasOrthonormalCols Q R hQ,
    moorePenroseInverse_eq_inv_of_isUnit R hR]
  calc
    _ = Q * (R * R⁻¹) * Qᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det R).mp hR),
      Matrix.mul_one]

private theorem integral_frobSq_rowVolume_error_eq_projection [Fintype r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (R : Matrix d d 𝕜) (hR : IsUnit R)
    (hT : 0 < rowSubsetVolume (Q * R) Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) (Y : Matrix n r 𝕜) :
    (∫ S, frobSq (Y - (Q * R) * (rowSubsetPseudoinverse (Q * R) S * Y))
      ∂rowVolumeLaw (Q * R) Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard)) =
    ∫ S, frobSq (Y - projectionVolumeInterpolant Q Y S) ∂projectionRowVolumeLaw Q hQ := by
  rw [rowVolumeLaw_eq_projectionRowVolumeLaw Q hQ R hR hT hcard,
    integral_projectionRowVolumeLaw, integral_projectionRowVolumeLaw]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hJ : 0 < rowSubsetVolume Q J.val
  · rw [mul_rowSubsetPseudoinverse_sizedSubset_mul_eq Q R hR J hJ Y]
  · have hz := le_antisymm (le_of_not_gt hJ) (rowSubsetVolume_nonneg Q J.val)
    rw [hz, zero_smul, zero_smul]

/-- **Sharp row-volume regression risk over `ℝ` or `ℂ`.** For the actual determinant-weighted
law on subsets of size equal to the design width, the fitted solution has expected squared
Frobenius residual at most `(d + 1)` times optimal. Full column rank is the positive Gram
normalizer `hT`. The total padded pseudoinverse is the literal inverse-selected-row solve
on every positive-mass subset (`rowSubsetPseudoinverse_sizedSubset_mul`).
Source: Dereziński–Warmuth 2018, Theorem 8, with singular subsets retained at zero mass.
atlas: row-volume-regression-error (partial) -/
theorem integral_frobSq_sub_mul_rowSubsetPseudoinverse_mul_le [Fintype r]
    (X : Matrix n d 𝕜) (Y : Matrix n r 𝕜)
    (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) :
    (∫ S, frobSq (Y - X * (rowSubsetPseudoinverse X S * Y))
      ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard)) ≤
      ((Fintype.card d : ℝ) + 1) * frobSq ((1 - X * moorePenroseInverse X) * Y) := by
  have hX : IsUnit (Xᴴ * X) := by
    have h := (rowSubsetVolume_pos_iff_isUnit X Finset.univ).mp hT
    simpa only [rowSubsetGram, coordinateSelector_univ, Matrix.mul_one] using h
  obtain ⟨Q, R, hQ, hR, rfl⟩ := exists_orthonormal_mul_isUnit_of_isUnit_gram X hX
  rw [integral_frobSq_rowVolume_error_eq_projection Q hQ R hR hT hcard,
    mul_moorePenroseInverse_mul_right_eq Q hQ R hR, ← residual_eq_one_sub_mul]
  exact integral_frobSq_projectionVolumeInterpolant_error_le Q hQ Y

/-- **Equality under general position.** If every size-width row restriction is nonsingular,
the row-volume regression risk is exactly `(d + 1)` times optimal. Without `hfull` the
inequality is the valid conclusion; no equality is asserted for singular zero-mass subsets.
Source: Dereziński–Warmuth 2018, Theorem 8, with the necessary full-support qualification.
atlas: row-volume-regression-error (partial) -/
theorem integral_frobSq_sub_mul_rowSubsetPseudoinverse_mul_eq_of_full_support [Fintype r]
    (X : Matrix n d 𝕜) (Y : Matrix n r 𝕜)
    (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n)
    (hfull : ∀ S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d),
      IsUnit (rowSubsetGram X S)) :
    (∫ S, frobSq (Y - X * (rowSubsetPseudoinverse X S * Y))
      ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard)) =
      ((Fintype.card d : ℝ) + 1) * frobSq ((1 - X * moorePenroseInverse X) * Y) := by
  have hX : IsUnit (Xᴴ * X) := by
    have h := (rowSubsetVolume_pos_iff_isUnit X Finset.univ).mp hT
    simpa only [rowSubsetGram, coordinateSelector_univ, Matrix.mul_one] using h
  obtain ⟨Q, R, hQ, hR, rfl⟩ := exists_orthonormal_mul_isUnit_of_isUnit_gram X hX
  rw [integral_frobSq_rowVolume_error_eq_projection Q hQ R hR hT hcard,
    mul_moorePenroseInverse_mul_right_eq Q hQ R hR, ← residual_eq_one_sub_mul]
  apply integral_frobSq_projectionVolumeInterpolant_error_eq_of_full_support Q hQ Y
  intro S hS
  have h := (rowSubsetVolume_pos_iff_isUnit (Q * R) S).mpr (hfull S hS)
  rw [rowSubsetVolume_mul_right] at h
  apply (rowSubsetVolume_pos_iff_isUnit Q S).mp
  exact pos_of_mul_pos_right h (sq_nonneg _)

open scoped Matrix.Norms.L2Operator in
private local instance : NormedSpace ℝ (Matrix n n 𝕜) where
  toModule := inferInstance
  norm_smul_le := by
    intro t A
    have he : t • A = (t : 𝕜) • A := by
      ext i j
      simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rw [he]
    simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul_le (t : 𝕜) A

omit [DecidableEq n] in
private theorem frobSq_mul_replicateCol_eq_re_quadForm (A : Matrix n n 𝕜) (v : n → 𝕜) :
    frobSq (A * Matrix.replicateCol Unit v) = RCLike.re (quadForm (Aᴴ * A) v) := by
  rw [quadForm_conjTranspose_mul_self, frobSq_eq_sum_norm_sq, dotProduct, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Finset.univ_unique,
    Finset.sum_singleton, Pi.star_apply, RCLike.star_def, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.ofReal_re, Matrix.mulVec, dotProduct]

omit [DecidableEq n] in
private theorem le_of_re_quadForm_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ v, RCLike.re (quadForm A v) ≤ RCLike.re (quadForm B v)) : A ≤ B := by
  apply Matrix.le_iff.mpr
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA)
  intro v
  change 0 ≤ quadForm (B - A) v
  rw [← (hB.sub hA).ofReal_re_quadForm v, RCLike.ofReal_nonneg]
  simpa only [quadForm, Matrix.sub_mulVec, dotProduct_sub, map_sub] using sub_nonneg.mpr (h v)

open scoped Matrix.Norms.L2Operator in
private theorem re_quadForm_integral_rowVolumeLaw (X : Matrix n d 𝕜)
    (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) (F : Finset n → Matrix n n 𝕜) (v : n → 𝕜) :
    RCLike.re (quadForm
      (∫ S, F S ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl
        (by simpa using hcard)) v) =
      ∫ S, RCLike.re (quadForm (F S) v)
        ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard) := by
  rw [integral_rowVolumeLaw, integral_rowVolumeLaw]
  simp only [quadForm, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
    dotProduct_smul, map_sum, RCLike.smul_re, smul_eq_mul]

omit [DecidableEq d] in
private theorem gram_one_sub_mul_moorePenroseInverse (X : Matrix n d 𝕜) :
    (1 - X * moorePenroseInverse X)ᴴ * (1 - X * moorePenroseInverse X) =
      1 - X * moorePenroseInverse X := by
  rw [(Matrix.isHermitian_one.sub (mul_moorePenroseInverse_isHermitian X)).eq]
  exact (mul_moorePenroseInverse_isIdempotentElem X).one_sub

open scoped Matrix.Norms.L2Operator in
/-- **Operator form of the row-volume regression bound.** The actual expected adjoint-product
error operator is at most `(d + 1)` times the orthogonal residual projector. This controls
every deterministic right-hand side simultaneously. Source: the quadratic-form consequence
of Dereziński–Warmuth 2018, Theorem 8, with zero-mass singular subsets retained.
atlas: row-volume-regression-error (partial) -/
theorem integral_conjTranspose_mul_rowVolume_error_le (X : Matrix n d 𝕜)
    (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) :
    (∫ S, (1 - X * rowSubsetPseudoinverse X S)ᴴ *
      (1 - X * rowSubsetPseudoinverse X S)
      ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard)) ≤
      ((Fintype.card d : ℝ) + 1) • (1 - X * moorePenroseInverse X) := by
  apply le_of_re_quadForm_le
  · exact Matrix.isHermitian_integral (Filter.Eventually.of_forall fun S =>
      Matrix.isHermitian_conjTranspose_mul_self _)
  · exact (Matrix.isHermitian_one.sub (mul_moorePenroseInverse_isHermitian X)).smul
      (by simp [IsSelfAdjoint])
  · intro v
    rw [re_quadForm_integral_rowVolumeLaw X hT hcard]
    have h := integral_frobSq_sub_mul_rowSubsetPseudoinverse_mul_le X
      (Matrix.replicateCol Unit v) hT hcard
    have hres (S : Finset n) :
        Matrix.replicateCol Unit v - X * (rowSubsetPseudoinverse X S *
          Matrix.replicateCol Unit v) =
        (1 - X * rowSubsetPseudoinverse X S) * Matrix.replicateCol Unit v := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    simp_rw [hres] at h
    simp only [frobSq_mul_replicateCol_eq_re_quadForm,
      gram_one_sub_mul_moorePenroseInverse] at h
    simpa only [quadForm, Matrix.smul_mulVec, dotProduct_smul, RCLike.smul_re] using h

open scoped Matrix.Norms.L2Operator in
/-- **Operator equality in general position.** When every size-width row restriction is
nonsingular, the expected adjoint-product error operator is exactly `(d + 1)` times the
orthogonal residual projector. Source: Dereziński–Warmuth 2018, Theorem 8.
atlas: row-volume-regression-error (partial) -/
theorem integral_conjTranspose_mul_rowVolume_error_eq_of_full_support (X : Matrix n d 𝕜)
    (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n)
    (hfull : ∀ S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d),
      IsUnit (rowSubsetGram X S)) :
    (∫ S, (1 - X * rowSubsetPseudoinverse X S)ᴴ *
      (1 - X * rowSubsetPseudoinverse X S)
      ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard)) =
      ((Fintype.card d : ℝ) + 1) • (1 - X * moorePenroseInverse X) := by
  apply le_antisymm (integral_conjTranspose_mul_rowVolume_error_le X hT hcard)
  apply le_of_re_quadForm_le
  · exact (Matrix.isHermitian_one.sub (mul_moorePenroseInverse_isHermitian X)).smul
      (by simp [IsSelfAdjoint])
  · exact Matrix.isHermitian_integral (Filter.Eventually.of_forall fun S =>
      Matrix.isHermitian_conjTranspose_mul_self _)
  · intro v
    rw [re_quadForm_integral_rowVolumeLaw X hT hcard]
    have h := integral_frobSq_sub_mul_rowSubsetPseudoinverse_mul_eq_of_full_support X
      (Matrix.replicateCol Unit v) hT hcard hfull
    have hres (S : Finset n) :
        Matrix.replicateCol Unit v - X * (rowSubsetPseudoinverse X S *
          Matrix.replicateCol Unit v) =
        (1 - X * rowSubsetPseudoinverse X S) * Matrix.replicateCol Unit v := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    simp_rw [hres] at h
    simp only [frobSq_mul_replicateCol_eq_re_quadForm,
      gram_one_sub_mul_moorePenroseInverse] at h
    simpa only [quadForm, Matrix.smul_mulVec, dotProduct_smul, RCLike.smul_re] using h.ge

/-- The sharp row-volume residual bound for any random subset with the actual native law.
Source: transport of the finite determinant-weighted regression theorem. -/
theorem integral_frobSq_sub_mul_rowSubsetPseudoinverse_mul_le_of_hasLaw [Fintype r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n d 𝕜) (Y : Matrix n r 𝕜)
    (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) (S : Ω → Finset n)
    (hS : HasLaw S (rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl
      (by simpa using hcard)) μ) :
    (∫ ω, frobSq (Y - X * (rowSubsetPseudoinverse X (S ω) * Y)) ∂μ) ≤
      ((Fintype.card d : ℝ) + 1) * frobSq ((1 - X * moorePenroseInverse X) * Y) := by
  calc
    _ = ∫ T, frobSq (Y - X * (rowSubsetPseudoinverse X T * Y))
        ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard) :=
      hS.integral_comp (show AEStronglyMeasurable _ _ from .of_discrete)
    _ ≤ _ := integral_frobSq_sub_mul_rowSubsetPseudoinverse_mul_le X Y hT hcard

/-- General-position equality for any realization of the actual row-volume law. -/
theorem integral_frobSq_sub_mul_rowSubsetPseudoinverse_mul_eq_of_hasLaw_of_full_support
    [Fintype r] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n d 𝕜) (Y : Matrix n r 𝕜)
    (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) (S : Ω → Finset n)
    (hS : HasLaw S (rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl
      (by simpa using hcard)) μ)
    (hfull : ∀ T ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d),
      IsUnit (rowSubsetGram X T)) :
    (∫ ω, frobSq (Y - X * (rowSubsetPseudoinverse X (S ω) * Y)) ∂μ) =
      ((Fintype.card d : ℝ) + 1) * frobSq ((1 - X * moorePenroseInverse X) * Y) := by
  calc
    _ = ∫ T, frobSq (Y - X * (rowSubsetPseudoinverse X T * Y))
        ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard) :=
      hS.integral_comp (show AEStronglyMeasurable _ _ from .of_discrete)
    _ = _ := integral_frobSq_sub_mul_rowSubsetPseudoinverse_mul_eq_of_full_support
      X Y hT hcard hfull

open scoped Matrix.Norms.L2Operator in
/-- The operator regression bound transports to every realization of the row-volume law. -/
theorem integral_conjTranspose_mul_rowVolume_error_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n d 𝕜) (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) (S : Ω → Finset n)
    (hS : HasLaw S (rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl
      (by simpa using hcard)) μ) :
    (∫ ω, (1 - X * rowSubsetPseudoinverse X (S ω))ᴴ *
      (1 - X * rowSubsetPseudoinverse X (S ω)) ∂μ) ≤
      ((Fintype.card d : ℝ) + 1) • (1 - X * moorePenroseInverse X) := by
  calc
    _ = ∫ T, (1 - X * rowSubsetPseudoinverse X T)ᴴ *
        (1 - X * rowSubsetPseudoinverse X T)
        ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard) :=
      hS.integral_comp (show AEStronglyMeasurable _ _ from .of_discrete)
    _ ≤ _ := integral_conjTranspose_mul_rowVolume_error_le X hT hcard

open scoped Matrix.Norms.L2Operator in
/-- The general-position operator equality under any realization of row-volume sampling. -/
theorem integral_conjTranspose_mul_rowVolume_error_eq_of_hasLaw_of_full_support
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n d 𝕜) (hT : 0 < rowSubsetVolume X Finset.univ)
    (hcard : Fintype.card d ≤ Fintype.card n) (S : Ω → Finset n)
    (hS : HasLaw S (rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl
      (by simpa using hcard)) μ)
    (hfull : ∀ T ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d),
      IsUnit (rowSubsetGram X T)) :
    (∫ ω, (1 - X * rowSubsetPseudoinverse X (S ω))ᴴ *
      (1 - X * rowSubsetPseudoinverse X (S ω)) ∂μ) =
      ((Fintype.card d : ℝ) + 1) • (1 - X * moorePenroseInverse X) := by
  calc
    _ = ∫ T, (1 - X * rowSubsetPseudoinverse X T)ᴴ *
        (1 - X * rowSubsetPseudoinverse X T)
        ∂rowVolumeLaw X Finset.univ (Fintype.card d) hT le_rfl (by simpa using hcard) :=
      hS.integral_comp (show AEStronglyMeasurable _ _ from .of_discrete)
    _ = _ := integral_conjTranspose_mul_rowVolume_error_eq_of_full_support X hT hcard hfull

end NLAlib
