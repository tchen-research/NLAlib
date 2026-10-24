import NLAlib.LowRank.Cholesky.ProjectorHistories
import NLAlib.Matrix.Factorizations.ProjectionPivoting
import NLAlib.Sketching.Sampling.ProjectionVolumeResidual

/-! # Adaptive projection pivoting realizes the projection-volume law

The actual real and complex Cholesky history laws on `Q Qᴴ` are the adaptive
QR squared-column-norm pivot laws on `Qᴴ`. Forgetting chronological order
gives exactly the native projection row-volume law. The already proved
fixed-input interpolation mean and sharp risk therefore apply to the
actual pivot sampler, rather than to an assumed subset certificate.
Source: Epperly 2025, Theorem 3.3; Dereziński–Warmuth 2018, Theorem 8.
Atlas: `adaptive-pivoting-projection-dpp`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder

namespace NLAlib

variable {n d r : Type*} [Fintype n] [Fintype d] [DecidableEq n] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
private local instance {𝕜 a b : Type*} [RCLike 𝕜]
    [Fintype a] [Fintype b] [DecidableEq b] : NormedSpace ℝ (Matrix a b 𝕜) where
  toModule := inferInstance
  norm_smul_le := by
    intro t A
    have he : t • A = (t : 𝕜) • A := by
      ext i j
      simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rw [he]
    simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul_le (t : 𝕜) A

private theorem real_pmf_image_mass [Nonempty n]
    (Q : Matrix n d ℝ) (hQ : HasOrthonormalCols Q) (S : Finset n) :
    (((choleskyHistoryPMF (Q * Qᴴ) (Matrix.posSemidef_self_mul_conjTranspose Q) (Fintype.card d)).map
      (fun h => Finset.univ.image h)) S).toReal =
      if S.card = Fintype.card d then rowSubsetVolume Q S else 0 := by
  have hRank : (Q * Qᴴ).rank = Fintype.card d := by
    rw [Matrix.rank_self_mul_conjTranspose, hQ.rank_eq_card]
  have h := choleskyHistoryPMF_projector_image_toReal_of_rank_eq
    (Matrix.isHermitian_mul_conjTranspose_self Q) (hQ.isIdempotentElem_mul_conjTranspose) hRank S
  rw [h]
  split_ifs with hS
  · exact re_det_rowGram_sizedSubset_eq_rowSubsetVolume Q ⟨S, hS⟩
  · rfl

private theorem complex_pmf_image_mass [Nonempty n]
    (Q : Matrix n d ℂ) (hQ : HasOrthonormalCols Q) (S : Finset n) :
    (((complexCholeskyHistoryPMF (Q * Qᴴ) (Matrix.posSemidef_self_mul_conjTranspose Q)
      (Fintype.card d)).map (fun h => Finset.univ.image h)) S).toReal =
      if S.card = Fintype.card d then rowSubsetVolume Q S else 0 := by
  have hRank : (Q * Qᴴ).rank = Fintype.card d := by
    rw [Matrix.rank_self_mul_conjTranspose, hQ.rank_eq_card]
  have h := complexCholeskyHistoryPMF_projector_image_toReal_of_rank_eq
    (Matrix.isHermitian_mul_conjTranspose_self Q) (hQ.isIdempotentElem_mul_conjTranspose) hRank S
  rw [h]
  split_ifs with hS
  · exact re_det_rowGram_sizedSubset_eq_rowSubsetVolume Q ⟨S, hS⟩
  · rfl

variable [Nonempty n] [MeasurableSpace n] [MeasurableSingletonClass n]

/-- The actual real adaptive QR pivot-history law: run the existing native
Cholesky process on the row Gram matrix for exactly the frame width. -/
def projectionPivotHistoryLaw (Q : Matrix n d ℝ) : Measure (Fin (Fintype.card d) → n) :=
  choleskyHistoryLaw (Q * Qᴴ) (Matrix.posSemidef_self_mul_conjTranspose Q) (Fintype.card d)

/-- The same actual adaptive pivot process on a complex frame, using the
native complex history law with real nonnegative transition probabilities. -/
def complexProjectionPivotHistoryLaw (Q : Matrix n d ℂ) : Measure (Fin (Fintype.card d) → n) :=
  complexCholeskyHistoryLaw (Q * Qᴴ) (Matrix.posSemidef_self_mul_conjTranspose Q) (Fintype.card d)

/-- Forgetting the chronological order of actual real QR pivots gives the
actual projection row-volume law, not merely the same formal weights.
Epperly 2025, Theorem 3.3.
atlas: adaptive-pivoting-projection-dpp (partial)-/
theorem hasLaw_image_projectionPivotHistoryLaw (Q : Matrix n d ℝ) (hQ : HasOrthonormalCols Q) :
    HasLaw (fun h : Fin (Fintype.card d) → n => Finset.univ.image h)
      (projectionRowVolumeLaw Q hQ) (projectionPivotHistoryLaw Q) := by
  have hm : Measurable (fun h : Fin (Fintype.card d) → n => Finset.univ.image h) := .of_discrete
  refine ⟨hm.aemeasurable, ?_⟩
  unfold projectionPivotHistoryLaw choleskyHistoryLaw
  rw [PMF.toMeasure_map _ _ hm]
  apply Measure.ext_of_measureReal_singleton
  intro S
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton S),
    real_pmf_image_mass Q hQ S, projectionRowVolumeLaw_singleton]

/-- The exact same subset-law realization for complex adaptive QR pivots.
No real-part matrix replacement is used. Epperly 2025, Theorem 3.3.
atlas: adaptive-pivoting-projection-dpp (partial)-/
theorem hasLaw_image_complexProjectionPivotHistoryLaw (Q : Matrix n d ℂ)
    (hQ : HasOrthonormalCols Q) :
    HasLaw (fun h : Fin (Fintype.card d) → n => Finset.univ.image h)
      (projectionRowVolumeLaw Q hQ) (complexProjectionPivotHistoryLaw Q) := by
  have hm : Measurable (fun h : Fin (Fintype.card d) → n => Finset.univ.image h) := .of_discrete
  refine ⟨hm.aemeasurable, ?_⟩
  unfold complexProjectionPivotHistoryLaw complexCholeskyHistoryLaw
  rw [PMF.toMeasure_map _ _ hm]
  apply Measure.ext_of_measureReal_singleton
  intro S
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton S),
    complex_pmf_image_mass Q hQ S, projectionRowVolumeLaw_singleton]

omit [Nonempty n] [MeasurableSpace n] [MeasurableSingletonClass n] in
private theorem ae_size_fullRank_projectionRowVolumeLaw {𝕜 : Type*} [RCLike 𝕜]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) :
    ∀ᵐ S ∂projectionRowVolumeLaw Q hQ,
      S.card = Fintype.card d ∧ IsUnit (rowSubsetGram Q S) := by
  apply ae_iff_of_countable.mpr
  intro S hS
  have hp : 0 < (projectionRowVolumeLaw Q hQ).real {S} :=
    ENNReal.toReal_pos hS (measure_ne_top _ _)
  rw [projectionRowVolumeLaw_singleton] at hp
  split_ifs at hp with hcard
  · exact ⟨hcard, (rowSubsetVolume_pos_iff_isUnit Q S).mp hp⟩
  · exact (lt_irrefl 0 hp).elim

omit [Fintype n] [Nonempty n] [MeasurableSpace n] [MeasurableSingletonClass n] in
private theorem injective_of_image_card_eq {t : ℕ} (h : Fin t → n)
    (hc : (Finset.univ.image h).card = t) : Function.Injective h := by
  have hi : Set.InjOn h (Finset.univ : Finset (Fin t)) :=
    Finset.card_image_iff.mp (by simpa only [Finset.card_univ, Fintype.card_fin] using hc)
  exact fun i j hij => hi (Finset.mem_univ i) (Finset.mem_univ j) hij

/-- The actual real pivot process almost surely selects distinct labels,
exactly the frame width in number, and an invertible selected row Gram.
Thus its selected square row matrix is nonsingular and every inverse fit
is defined on its support. Epperly 2025, Theorem 3.3.
atlas: adaptive-pivoting-projection-dpp (partial)-/
theorem ae_injective_fullRank_projectionPivotHistoryLaw
    (Q : Matrix n d ℝ) (hQ : HasOrthonormalCols Q) :
    ∀ᵐ h ∂projectionPivotHistoryLaw Q, Function.Injective h ∧
      IsUnit (rowSubsetGram Q (Finset.univ.image h)) := by
  have hS := (hasLaw_image_projectionPivotHistoryLaw Q hQ).ae_iff
    (show Measurable (fun S : Finset n => S.card = Fintype.card d ∧ IsUnit (rowSubsetGram Q S))
      from .of_discrete)
  have hA := hS.mpr (ae_size_fullRank_projectionRowVolumeLaw Q hQ)
  filter_upwards [hA] with h hh
  exact ⟨injective_of_image_card_eq h hh.1, hh.2⟩

/-- Distinct supported pivots and nonsingular final row restriction for the
actual complex adaptive process. Epperly 2025, Theorem 3.3.
atlas: adaptive-pivoting-projection-dpp (partial)-/
theorem ae_injective_fullRank_complexProjectionPivotHistoryLaw
    (Q : Matrix n d ℂ) (hQ : HasOrthonormalCols Q) :
    ∀ᵐ h ∂complexProjectionPivotHistoryLaw Q, Function.Injective h ∧
      IsUnit (rowSubsetGram Q (Finset.univ.image h)) := by
  have hS := (hasLaw_image_complexProjectionPivotHistoryLaw Q hQ).ae_iff
    (show Measurable (fun S : Finset n => S.card = Fintype.card d ∧ IsUnit (rowSubsetGram Q S))
      from .of_discrete)
  have hA := hS.mpr (ae_size_fullRank_projectionRowVolumeLaw Q hQ)
  filter_upwards [hA] with h hh
  exact ⟨injective_of_image_card_eq h hh.1, hh.2⟩

open scoped Matrix.Norms.L2Operator in
/-- The interpolation produced by actual real adaptive projection pivots is
unbiased for the fixed input's orthogonal projection.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem integral_projectionPivotInterpolant [Fintype r] [DecidableEq r]
    (Q : Matrix n d ℝ) (hQ : HasOrthonormalCols Q) (A : Matrix n r ℝ) :
    (∫ h, projectionVolumeInterpolant Q A (Finset.univ.image h) ∂projectionPivotHistoryLaw Q) =
      Q * (Qᴴ * A) :=
  integral_projectionVolumeInterpolant_of_hasLaw _ Q hQ A _
    (hasLaw_image_projectionPivotHistoryLaw Q hQ)

open scoped Matrix.Norms.L2Operator in
/-- The unbiased interpolation mean for the actual complex adaptive pivot
process, with the literal selected-row inverse on its proved support.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem integral_complexProjectionPivotInterpolant [Fintype r] [DecidableEq r]
    (Q : Matrix n d ℂ) (hQ : HasOrthonormalCols Q) (A : Matrix n r ℂ) :
    (∫ h, projectionVolumeInterpolant Q A (Finset.univ.image h)
      ∂complexProjectionPivotHistoryLaw Q) = Q * (Qᴴ * A) :=
  integral_projectionVolumeInterpolant_of_hasLaw _ Q hQ A _
    (hasLaw_image_complexProjectionPivotHistoryLaw Q hQ)

/-- Actual real adaptive projection pivoting has sharp interpolation risk
at most `(k+1)` times the optimal fixed-range residual. No general-position
hypothesis is imposed. Dereziński–Warmuth 2018, Theorem 8, support-correct form.
atlas: adaptive-pivoting-projection-dpp (partial)-/
theorem integral_frobSq_projectionPivotInterpolant_error_le [Fintype r]
    (Q : Matrix n d ℝ) (hQ : HasOrthonormalCols Q) (A : Matrix n r ℝ) :
    (∫ h, frobSq (A - projectionVolumeInterpolant Q A (Finset.univ.image h))
      ∂projectionPivotHistoryLaw Q) ≤
      ((Fintype.card d : ℝ) + 1) * frobSq (projResidual Q A) :=
  integral_frobSq_projectionVolumeInterpolant_error_le_of_hasLaw _ Q hQ A _
    (hasLaw_image_projectionPivotHistoryLaw Q hQ)

/-- The same sharp interpolation risk for actual complex adaptive pivots.
The bound is an inequality unless full selected-size support is supplied.
atlas: adaptive-pivoting-projection-dpp (partial)-/
theorem integral_frobSq_complexProjectionPivotInterpolant_error_le [Fintype r]
    (Q : Matrix n d ℂ) (hQ : HasOrthonormalCols Q) (A : Matrix n r ℂ) :
    (∫ h, frobSq (A - projectionVolumeInterpolant Q A (Finset.univ.image h))
      ∂complexProjectionPivotHistoryLaw Q) ≤
      ((Fintype.card d : ℝ) + 1) * frobSq (projResidual Q A) :=
  integral_frobSq_projectionVolumeInterpolant_error_le_of_hasLaw _ Q hQ A _
    (hasLaw_image_complexProjectionPivotHistoryLaw Q hQ)

/-- Real adaptive-pivot interpolation attains the sharp risk equality if
every size-width row restriction of the frame has full rank.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem integral_frobSq_projectionPivotInterpolant_error_eq_of_full_support [Fintype r]
    (Q : Matrix n d ℝ) (hQ : HasOrthonormalCols Q) (A : Matrix n r ℝ)
    (hfull : ∀ S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d),
      IsUnit (rowSubsetGram Q S)) :
    (∫ h, frobSq (A - projectionVolumeInterpolant Q A (Finset.univ.image h))
      ∂projectionPivotHistoryLaw Q) =
      ((Fintype.card d : ℝ) + 1) * frobSq (projResidual Q A) := by
  have h := (hasLaw_image_projectionPivotHistoryLaw Q hQ).integral_comp
    (show AEStronglyMeasurable (fun S => frobSq (A - projectionVolumeInterpolant Q A S))
      (projectionRowVolumeLaw Q hQ) from .of_discrete)
  exact h.trans (integral_frobSq_projectionVolumeInterpolant_error_eq_of_full_support Q hQ A hfull)

/-- The full-support equality for complex adaptive-pivot interpolation.
No unconditional equality is asserted at zero-mass singular subsets.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem integral_frobSq_complexProjectionPivotInterpolant_error_eq_of_full_support [Fintype r]
    (Q : Matrix n d ℂ) (hQ : HasOrthonormalCols Q) (A : Matrix n r ℂ)
    (hfull : ∀ S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card d),
      IsUnit (rowSubsetGram Q S)) :
    (∫ h, frobSq (A - projectionVolumeInterpolant Q A (Finset.univ.image h))
      ∂complexProjectionPivotHistoryLaw Q) =
      ((Fintype.card d : ℝ) + 1) * frobSq (projResidual Q A) := by
  have h := (hasLaw_image_complexProjectionPivotHistoryLaw Q hQ).integral_comp
    (show AEStronglyMeasurable (fun S => frobSq (A - projectionVolumeInterpolant Q A S))
      (projectionRowVolumeLaw Q hQ) from .of_discrete)
  exact h.trans (integral_frobSq_projectionVolumeInterpolant_error_eq_of_full_support Q hQ A hfull)

/-- Any realization of the actual real adaptive history law inherits the
proved projection-DPP subset law by forgetting pivot order. -/
theorem hasLaw_image_projectionPivotHistoryLaw_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Matrix n d ℝ) (hQ : HasOrthonormalCols Q)
    (H : Ω → Fin (Fintype.card d) → n) (hH : HasLaw H (projectionPivotHistoryLaw Q) μ) :
    HasLaw (fun ω => Finset.univ.image (H ω)) (projectionRowVolumeLaw Q hQ) μ := by
  simpa only [Function.comp_def] using (hasLaw_image_projectionPivotHistoryLaw Q hQ).comp hH

/-- The corresponding law transport for complex adaptive pivot histories. -/
theorem hasLaw_image_complexProjectionPivotHistoryLaw_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Matrix n d ℂ) (hQ : HasOrthonormalCols Q)
    (H : Ω → Fin (Fintype.card d) → n) (hH : HasLaw H (complexProjectionPivotHistoryLaw Q) μ) :
    HasLaw (fun ω => Finset.univ.image (H ω)) (projectionRowVolumeLaw Q hQ) μ := by
  simpa only [Function.comp_def] using (hasLaw_image_complexProjectionPivotHistoryLaw Q hQ).comp hH

end NLAlib
