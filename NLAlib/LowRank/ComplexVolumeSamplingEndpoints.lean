import NLAlib.LowRank.ComplexVolumeSamplingError
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Exact degenerate clauses for the actual complex volume law

Empty samples use the zero projector and deterministic empty subset law;
exact-rank samples recover the matrix almost surely. Above rank every weight
is zero and no positive normalization exists. Source: `sa:volume-theorem`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical Matrix Matrix.Norms.Frobenius ComplexOrder ENNReal
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The actual complex projector of a zero column operator is zero.
Source: `sa:volume`, empty-span convention. -/
@[simp] theorem complexColumnProjector_zero :
    complexColumnProjector (0 : Matrix m n ℂ) = 0 := by
  have hspace : complexColumnSpace (0 : Matrix m n ℂ) = ⊥ := by
    simp only [complexColumnSpace, map_zero, LinearMap.range_zero]
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_complexColumnProjector, hspace, Submodule.starProjection_bot, map_zero]
  rfl

omit [Fintype n] in
/-- The actual empty complex sample has zero orthogonal projector.
Source: `sa:volume`, its projector `P_∅=0`. -/
@[simp] theorem complexColumnProjector_complexVolumeSampleColumns_empty (A : Matrix m n ℂ) :
    complexColumnProjector (complexVolumeSampleColumns A ∅) = 0 := by
  rw [show complexVolumeSampleColumns A ∅ = 0 from Subsingleton.elim _ _]
  exact complexColumnProjector_zero

omit [Fintype n] in
/-- The actual complex residual of the empty sample is the whole input.
Source: `sa:volume`, empty-sample endpoint. -/
@[simp] theorem complexVolumeSamplingResidual_empty (A : Matrix m n ℂ) :
    complexVolumeSamplingResidual A ∅ = A := by
  simp only [complexVolumeSamplingResidual,
    complexColumnProjector_complexVolumeSampleColumns_empty, Matrix.zero_mul, sub_zero]

omit [DecidableEq m] in
/-- Sampling zero columns gives the literal deterministic empty-subset law.
Source: `sa:volume-theorem`, actual `k=0` probability endpoint. -/
theorem complexVolumeSamplingLaw_zero_eq_dirac (A : Matrix m n ℂ) :
    complexVolumeSamplingLaw A (show 0 ≤ A.rank from Nat.zero_le _) = Measure.dirac ∅ := by
  apply Measure.ext_of_measureReal_singleton
  intro S
  rw [measureReal_def, complexVolumeSamplingLaw_singleton,
    complexVolumeSamplingNormalizer_zero]
  by_cases hS : S = ∅
  · subst S
    simp [measureReal_def]
  · have hc : S.card ≠ 0 := fun h => hS (Finset.card_eq_zero.mp h)
    simp [hc, hS, measureReal_def]

/-- The actual expected error at sample size zero is exactly the complex
input Frobenius norm squared. Source: `sa:volume-theorem`. -/
theorem integral_complexVolumeSampling_residual_norm_sq_zero (A : Matrix m n ℂ) :
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2
      ∂complexVolumeSamplingLaw A (show 0 ≤ A.rank from Nat.zero_le _)) = ‖A‖ ^ 2 := by
  rw [complexVolumeSamplingLaw_zero_eq_dirac, integral_dirac, complexVolumeSamplingResidual_empty]

omit [DecidableEq m] in
/-- Above rank every prescribed complex Gram weight is zero.
Source: `sa:volume-theorem`, impossible-normalization endpoint. -/
theorem complexVolumeSamplingWeight_eq_zero_of_card_gt_rank
    (A : Matrix m n ℂ) {S : Finset n} (hS : A.rank < S.card) :
    complexVolumeSamplingWeight A S = 0 := by
  have hz := complexVolumeSamplingNormalizer_eq_zero_of_rank_lt A hS
  unfold complexVolumeSamplingNormalizer at hz
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun T _ => complexVolumeSamplingWeight_nonneg A T)).mp hz S
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩)

omit [DecidableEq m] in
/-- A positive normalizer cannot be assigned to the all-zero volume weights
above the input rank. Source: `sa:volume-theorem`, no normalized law for `k>rank A`. -/
theorem not_exists_positive_complexVolumeNormalizer_of_rank_lt
    (A : Matrix m n ℂ) {k : ℕ} (hk : A.rank < k) :
    ¬ ∃ Z : ℝ, 0 < Z ∧ (∑ S ∈ Finset.univ.powersetCard k, complexVolumeSamplingWeight A S) = Z := by
  rintro ⟨Z, hZ, he⟩
  have hz := complexVolumeSamplingNormalizer_eq_zero_of_rank_lt A hk
  change (∑ S ∈ Finset.univ.powersetCard k, complexVolumeSamplingWeight A S) = 0 at hz
  rw [hz] at he
  exact hZ.ne' he.symm

/-- At the exact complex input rank the genuine volume law recovers the
matrix almost surely, including rank zero and empty dimensions.
Source: `sa:volume-theorem`, its almost-sure exact-rank clause.
atlas: volume-sampling (partial) -/
theorem ae_complexVolumeSamplingResidual_rank_eq_zero (A : Matrix m n ℂ) :
    ∀ᵐ S ∂complexVolumeSamplingLaw A (le_refl A.rank), complexVolumeSamplingResidual A S = 0 := by
  rw [ae_iff_of_countable]
  intro S hS
  have hp := ENNReal.toReal_pos hS (measure_ne_top _ _)
  obtain ⟨hcard, hw⟩ := (complexVolumeSamplingLaw_singleton_pos_iff A (le_refl A.rank) S).mp hp
  exact complexVolumeSamplingResidual_eq_zero_of_card_eq_rank A hcard hw

end NLAlib
