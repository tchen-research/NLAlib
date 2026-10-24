import NLAlib.Sketching.Sampling.RowVolumePseudoinverse
import NLAlib.Matrix.Basic.CramerFrobenius
import NLAlib.Matrix.Basic.OrthonormalColumnReplacement

/-! # Projection-volume interpolation and its sharp residual moment

The subset law is the actual size-width row-volume law of an orthonormal
frame. Cramer's rule and Cauchy–Binet give the sharp fixed-input residual
moment. Singular subsets retain zero mass; their omitted Cramer minors
explain why equality requires full support at the selected size.
Source: Dereziński–Warmuth 2018, Theorems 5 and 8; Epperly, Theorem 3.3.
Atlas: `adaptive-pivoting-projection-dpp`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {𝕜 n d r : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
private local instance {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b] :
    NormedSpace ℝ (Matrix a b 𝕜) where
  toModule := inferInstance
  norm_smul_le := by
    intro t A
    have he : t • A = (t : 𝕜) • A := by
      ext i j
      simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rw [he]
    simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul_le (t : 𝕜) A

/-- An orthonormal frame has unit total row-volume normalizer. -/
theorem rowSubsetVolume_univ_of_orthonormal (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) :
    rowSubsetVolume Q Finset.univ = 1 := by
  simp only [rowSubsetVolume, rowSubsetGram, coordinateSelector_univ,
    Matrix.mul_one, hQ.conjTranspose_mul_self, Matrix.det_one, RCLike.one_re]

/-- The actual projection DPP subset law, as the native row-volume law at
sample size equal to the frame width. All size and normalization certificates
follow from orthonormality. -/
def projectionRowVolumeLaw (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) : Measure (Finset n) :=
  rowVolumeLaw Q Finset.univ (Fintype.card d)
    (by rw [rowSubsetVolume_univ_of_orthonormal Q hQ]; exact zero_lt_one) le_rfl
    (by simpa only [Finset.card_univ] using card_le_card_of_hasOrthonormalCols hQ)

/-- The projection row-volume law is a probability measure, also at width zero. -/
instance projectionRowVolumeLaw_isProbabilityMeasure (Q : Matrix n d 𝕜)
    (hQ : HasOrthonormalCols Q) : IsProbabilityMeasure (projectionRowVolumeLaw Q hQ) := by
  unfold projectionRowVolumeLaw
  infer_instance

/-- The actual projection subset law assigns each size-width set precisely
its row-volume determinant, and zero mass to every other size.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem projectionRowVolumeLaw_singleton (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q)
    (S : Finset n) :
    (projectionRowVolumeLaw Q hQ).real {S} =
      if S.card = Fintype.card d then rowSubsetVolume Q S else 0 := by
  unfold projectionRowVolumeLaw
  rw [rowVolumeLaw_singleton, rowSubsetVolume_univ_of_orthonormal Q hQ]
  simp [rowVolumeWeight]

/-- Integration against the actual projection subset law is its literal
squared-minor weighted sum over all size-width subsets. -/
theorem integral_projectionRowVolumeLaw {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q)
    (f : Finset n → E) :
    (∫ S, f S ∂projectionRowVolumeLaw Q hQ) =
      ∑ J : SizedSubset n d, rowSubsetVolume Q J.val • f J.val := by
  classical
  unfold projectionRowVolumeLaw
  rw [integral_rowVolumeLaw_eq_inv_smul_sum, rowSubsetVolume_univ_of_orthonormal Q hQ]
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_mul, inv_one, one_smul]
  rw [← Finset.sum_attach]
  let e : {S // S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d)} ≃ SizedSubset n d :=
    Equiv.subtypeEquivRight fun S => by simp
  rw [← e.sum_comp]
  rfl

private theorem sum_cramer_minor_sq_of_orthonormal [Fintype r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (E : Matrix n r 𝕜)
    (hE : Qᴴ * E = 0) :
    (∑ J : SizedSubset n d, ∑ i, ∑ j,
      ‖((Q.updateCol i (fun a => E a j)).submatrix (sizedSubsetIndex J) id).det‖ ^ 2) =
      (Fintype.card d : ℝ) * frobSq E := by
  have he (j : r) : Qᴴ *ᵥ (fun a => E a j) = 0 := by
    funext i
    exact congrFun (congrFun hE i) j
  have hdet (i : d) (j : r) :
      (∑ J : SizedSubset n d,
        ‖((Q.updateCol i (fun a => E a j)).submatrix (sizedSubsetIndex J) id).det‖ ^ 2) =
      ∑ a, ‖E a j‖ ^ 2 := by
    have h := congrArg RCLike.re (det_conjTranspose_mul_self_eq_sum_norm_sq
      (Q.updateCol i (fun a => E a j)))
    rw [RCLike.ofReal_re] at h
    rw [← h]
    exact re_det_gram_updateCol_of_orthonormal Q hQ _ (he j) i
  calc
    _ = ∑ i, ∑ j, ∑ J : SizedSubset n d,
        ‖((Q.updateCol i (fun a => E a j)).submatrix (sizedSubsetIndex J) id).det‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hdet]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        frobSq_eq_sum_norm_sq, Finset.sum_comm]

/-- The exact fixed-input Cramer residual moment is at most the frame width
times the residual Frobenius square. Singular subsets have their actual zero
mass, and their Cramer minor squares are only added on the upper-bound side.
Source: Dereziński–Warmuth 2018, proof of Theorem 8. -/
theorem integral_frobSq_projectionRowVolume_solve_le [Fintype r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (E : Matrix n r 𝕜)
    (hE : Qᴴ * E = 0) :
    (∫ S, frobSq (rowSubsetPseudoinverse Q S * E) ∂projectionRowVolumeLaw Q hQ) ≤
      (Fintype.card d : ℝ) * frobSq E := by
  rw [integral_projectionRowVolumeLaw]
  calc
    _ ≤ ∑ J : SizedSubset n d, ∑ i, ∑ j,
        ‖((Q.updateCol i (fun a => E a j)).submatrix (sizedSubsetIndex J) id).det‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro J _
      by_cases hJ : 0 < rowSubsetVolume Q J.val
      · exact le_of_eq (rowSubsetVolume_mul_frobSq_pseudoinverse_mul Q J hJ E)
      · have hz := le_antisymm (le_of_not_gt hJ) (rowSubsetVolume_nonneg Q J.val)
        simp only [hz, smul_eq_mul, zero_mul]
        positivity
    _ = _ := sum_cramer_minor_sq_of_orthonormal Q hQ E hE

/-- Full support at the selected width makes the fixed-input Cramer residual
moment an equality. Smaller row restrictions need not have full rank. -/
theorem integral_frobSq_projectionRowVolume_solve_eq_of_full_support [Fintype r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (E : Matrix n r 𝕜)
    (hE : Qᴴ * E = 0)
    (hfull : ∀ S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d),
      IsUnit (rowSubsetGram Q S)) :
    (∫ S, frobSq (rowSubsetPseudoinverse Q S * E) ∂projectionRowVolumeLaw Q hQ) =
      (Fintype.card d : ℝ) * frobSq E := by
  rw [integral_projectionRowVolumeLaw]
  calc
    _ = ∑ J : SizedSubset n d, ∑ i, ∑ j,
        ‖((Q.updateCol i (fun a => E a j)).submatrix (sizedSubsetIndex J) id).det‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro J _
      exact rowSubsetVolume_mul_frobSq_pseudoinverse_mul Q J
        ((rowSubsetVolume_pos_iff_isUnit Q J.val).mpr (hfull J.val (by simp [J.property]))) E
    _ = _ := sum_cramer_minor_sq_of_orthonormal Q hQ E hE

/-- The one-vector version of the Cramer residual moment, expressed with the
actual padded inverse-vector product and Euclidean squared coordinate norm. -/
theorem integral_sum_norm_sq_projectionRowVolume_solve_le
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (e : n → 𝕜)
    (he : Qᴴ *ᵥ e = 0) :
    (∫ S, ∑ i, ‖(rowSubsetPseudoinverse Q S *ᵥ e) i‖ ^ 2 ∂projectionRowVolumeLaw Q hQ) ≤
      (Fintype.card d : ℝ) * ∑ a, ‖e a‖ ^ 2 := by
  let E : Matrix n (Fin 1) 𝕜 := fun a _ => e a
  have hE : Qᴴ * E = 0 := by
    ext i j
    exact congrFun he i
  have h := integral_frobSq_projectionRowVolume_solve_le Q hQ E hE
  simpa only [frobSq_eq_sum_norm_sq, Fin.sum_univ_one, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, E] using h

/-- The total projection-volume interpolation estimator. On the supported
size-width subsets it is exactly `Q * Q_S⁻¹ * A_S`; the definition also covers
the zero-mass singular subsets using the native padded pseudoinverse. -/
def projectionVolumeInterpolant [Fintype r] (Q : Matrix n d 𝕜) (A : Matrix n r 𝕜)
    (S : Finset n) : Matrix n r 𝕜 := Q * (rowSubsetPseudoinverse Q S * A)

/-- On every supported full-size subset the estimator uses exactly the
literal sampled rows and their square inverse.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem projectionVolumeInterpolant_sizedSubset [Fintype r]
    (Q : Matrix n d 𝕜) (A : Matrix n r 𝕜) (J : SizedSubset n d)
    (hJ : 0 < rowSubsetVolume Q J.val) :
    projectionVolumeInterpolant Q A J.val =
      Q * ((Q.submatrix (sizedSubsetIndex J) id)⁻¹ * A.submatrix (sizedSubsetIndex J) id) := by
  rw [projectionVolumeInterpolant, rowSubsetPseudoinverse_sizedSubset_mul Q J hJ A]

open scoped Matrix.Norms.L2Operator in
/-- Projection-volume interpolation is unbiased for the orthogonal projection
of every fixed right-hand-side matrix, without a general-position assumption. -/
theorem integral_projectionVolumeInterpolant [Fintype r] [DecidableEq r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (A : Matrix n r 𝕜) :
    (∫ S, projectionVolumeInterpolant Q A S ∂projectionRowVolumeLaw Q hQ) = Q * (Qᴴ * A) := by
  have hmean := integral_rowSubsetPseudoinverse_mul Q Finset.univ (Fintype.card d)
    (by rw [rowSubsetVolume_univ_of_orthonormal Q hQ]; exact zero_lt_one) le_rfl
    (by simpa only [Finset.card_univ] using card_le_card_of_hasOrthonormalCols hQ) A
  simp only [rowSubsetPseudoinverse_univ, hQ.moorePenroseInverse_eq_conjTranspose] at hmean
  calc
    _ = Q * (∫ S, rowSubsetPseudoinverse Q S * A ∂projectionRowVolumeLaw Q hQ) := by
      rw [integral_projectionRowVolumeLaw, integral_projectionRowVolumeLaw]
      simp only [projectionVolumeInterpolant, Matrix.mul_sum, Matrix.mul_smul]
    _ = _ := congrArg (fun B => Q * B) hmean

/-- The actual projection-volume interpolation risk is exactly the fixed
projection residual plus its Cramer solved-coordinate second moment. This
identity remains valid without full support. -/
theorem integral_frobSq_projectionVolumeInterpolant_error_eq [Fintype r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (A : Matrix n r 𝕜) :
    (∫ S, frobSq (A - projectionVolumeInterpolant Q A S) ∂projectionRowVolumeLaw Q hQ) =
      frobSq (projResidual Q A) +
        ∫ S, frobSq (rowSubsetPseudoinverse Q S * projResidual Q A) ∂projectionRowVolumeLaw Q hQ := by
  have heq : (∫ S, frobSq (A - projectionVolumeInterpolant Q A S) ∂projectionRowVolumeLaw Q hQ) =
      ∫ S, (frobSq (projResidual Q A) + frobSq (rowSubsetPseudoinverse Q S * projResidual Q A))
        ∂projectionRowVolumeLaw Q hQ := by
    rw [integral_projectionRowVolumeLaw, integral_projectionRowVolumeLaw]
    apply Finset.sum_congr rfl
    intro J _
    by_cases hJ : 0 < rowSubsetVolume Q J.val
    · rw [projectionVolumeInterpolant, frobSq_rowSubset_interpolation_error Q hQ J.val
        ((rowSubsetVolume_pos_iff_isUnit Q J.val).mp hJ)]
    · have hz := le_antisymm (le_of_not_gt hJ) (rowSubsetVolume_nonneg Q J.val)
      rw [hz, zero_smul, zero_smul]
  rw [heq, integral_add (.of_finite) (.of_finite)]
  simp

/-- The sharp fixed-input projection-volume interpolation risk is bounded by
`(width+1)` times the true projection residual square. Only the sampled rows of
the input are used by the supported inverse-selected-row solve.
Source: Dereziński–Warmuth 2018, Theorem 8 with the necessary support correction. -/
theorem integral_frobSq_projectionVolumeInterpolant_error_le [Fintype r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (A : Matrix n r 𝕜) :
    (∫ S, frobSq (A - projectionVolumeInterpolant Q A S) ∂projectionRowVolumeLaw Q hQ) ≤
      ((Fintype.card d : ℝ) + 1) * frobSq (projResidual Q A) := by
  rw [integral_frobSq_projectionVolumeInterpolant_error_eq]
  have h := integral_frobSq_projectionRowVolume_solve_le Q hQ (projResidual Q A)
    (conjTranspose_mul_residual hQ A)
  linarith

/-- Full support at the selected width gives equality in the sharp
projection-volume interpolation risk. Without that hypothesis only the
inequality is asserted. -/
theorem integral_frobSq_projectionVolumeInterpolant_error_eq_of_full_support [Fintype r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (A : Matrix n r 𝕜)
    (hfull : ∀ S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d),
      IsUnit (rowSubsetGram Q S)) :
    (∫ S, frobSq (A - projectionVolumeInterpolant Q A S) ∂projectionRowVolumeLaw Q hQ) =
      ((Fintype.card d : ℝ) + 1) * frobSq (projResidual Q A) := by
  rw [integral_frobSq_projectionVolumeInterpolant_error_eq,
    integral_frobSq_projectionRowVolume_solve_eq_of_full_support Q hQ (projResidual Q A)
      (conjTranspose_mul_residual hQ A) hfull]
  ring

open scoped Matrix.Norms.L2Operator in
/-- Unbiased interpolation transports to any probability space carrying the
actual projection row-volume law. -/
theorem integral_projectionVolumeInterpolant_of_hasLaw [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (A : Matrix n r 𝕜)
    (R : Ω → Finset n) (hR : HasLaw R (projectionRowVolumeLaw Q hQ) μ) :
    (∫ ω, projectionVolumeInterpolant Q A (R ω) ∂μ) = Q * (Qᴴ * A) := by
  calc
    _ = ∫ S, projectionVolumeInterpolant Q A S ∂projectionRowVolumeLaw Q hQ :=
      hR.integral_comp (show AEStronglyMeasurable (projectionVolumeInterpolant Q A)
        (projectionRowVolumeLaw Q hQ) from .of_discrete)
    _ = _ := integral_projectionVolumeInterpolant Q hQ A

/-- The sharp interpolation risk transports to every realization whose
subset law is the actual projection row-volume law. -/
theorem integral_frobSq_projectionVolumeInterpolant_error_le_of_hasLaw [Fintype r]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (A : Matrix n r 𝕜)
    (R : Ω → Finset n) (hR : HasLaw R (projectionRowVolumeLaw Q hQ) μ) :
    (∫ ω, frobSq (A - projectionVolumeInterpolant Q A (R ω)) ∂μ) ≤
      ((Fintype.card d : ℝ) + 1) * frobSq (projResidual Q A) := by
  calc
    _ = ∫ S, frobSq (A - projectionVolumeInterpolant Q A S) ∂projectionRowVolumeLaw Q hQ :=
      hR.integral_comp (show AEStronglyMeasurable
        (fun S => frobSq (A - projectionVolumeInterpolant Q A S))
        (projectionRowVolumeLaw Q hQ) from .of_discrete)
    _ ≤ _ := integral_frobSq_projectionVolumeInterpolant_error_le Q hQ A

end NLAlib
