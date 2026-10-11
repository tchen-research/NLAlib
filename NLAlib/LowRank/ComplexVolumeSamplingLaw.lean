import NLAlib.Matrix.ComplexVolumeProjection
import NLAlib.Matrix.ComplexVolumeSpectrum
import NLAlib.Sketching.FiniteSampling

/-!
# Actual complex determinant-weighted subset law

Nonnegative complex Gram determinants define a literal finite probability
law exactly at feasible ranks. No zero normalizer is used to manufacture a
law above the input rank. Source: `sa:volume`; atlas `volume-sampling`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical Matrix ComplexOrder NNReal ENNReal
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The actual complex columns selected by their original finite labels.
Source: operator re-derivation `sa:volume`, its matrix `A_S`. -/
def complexVolumeSampleColumns (A : Matrix m n ℂ) (S : Finset n) : Matrix m S ℂ :=
  A.submatrix id Subtype.val

/-- The real nonnegative determinant of the actual selected complex Gram.
Source: `sa:volume`, its weight `w(S)`. -/
def complexVolumeSamplingWeight (A : Matrix m n ℂ) (S : Finset n) : ℝ :=
  ((complexVolumeSampleColumns A S)ᴴ * complexVolumeSampleColumns A S).det.re

/-- The sum of all actual prescribed-size complex Gram weights.
Source: `sa:volume`, its normalizer `Z_k`. -/
def complexVolumeSamplingNormalizer (A : Matrix m n ℂ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k, complexVolumeSamplingWeight A S

/-- The actual orthogonal-projection residual for a complex column sample.
Source: `sa:volume-theorem`, its residual `A−P_S A`. -/
def complexVolumeSamplingResidual [DecidableEq m] (A : Matrix m n ℂ) (S : Finset n) : Matrix m n ℂ :=
  A - complexColumnProjector (complexVolumeSampleColumns A S) * A

omit [Fintype n] [DecidableEq n] in
/-- Selected complex Gram matrices are the corresponding full Gram minors.
Source: `sa:volume`, principal-minor representation. -/
theorem conjTranspose_complexVolumeSampleColumns_mul_eq_submatrix
    (A : Matrix m n ℂ) (S : Finset n) :
    (complexVolumeSampleColumns A S)ᴴ * complexVolumeSampleColumns A S =
      (Aᴴ * A).submatrix (Subtype.val : S → n) (Subtype.val : S → n) := rfl

/-- The actual complex determinant weight is nonnegative at every rank.
Source: positive complex Gram matrices, `sa:volume`. -/
theorem complexVolumeSamplingWeight_nonneg (A : Matrix m n ℂ) (S : Finset n) :
    0 ≤ complexVolumeSamplingWeight A S :=
  (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self
    (complexVolumeSampleColumns A S)).det_nonneg).1

/-- The complex determinant normalizer is the actual elementary Gram
eigenvalue sum. Source: `sa:volume`, determinant coefficient identity. -/
theorem complexVolumeSamplingNormalizer_eq_elementary (A : Matrix m n ℂ) (k : ℕ) :
    complexVolumeSamplingNormalizer A k = complexGramElementary A k := by
  exact sum_re_det_complex_gram_principal_minors_eq A k

/-- The actual normalizer is positive exactly for sample sizes no larger
than the complex input rank, including size zero and rank zero.
Source: `sa:volume`, feasible-law condition.
atlas: volume-sampling (partial) -/
theorem complexVolumeSamplingNormalizer_pos_iff (A : Matrix m n ℂ) (k : ℕ) :
    0 < complexVolumeSamplingNormalizer A k ↔ k ≤ A.rank := by
  rw [complexVolumeSamplingNormalizer_eq_elementary, complexGramElementary_pos_iff]

/-- Above the complex input rank the normalizer is zero, and the normalized
law is unavailable. Source: `sa:volume`, infeasible-size endpoint. -/
theorem complexVolumeSamplingNormalizer_eq_zero_of_rank_lt
    (A : Matrix m n ℂ) {k : ℕ} (hk : A.rank < k) :
    complexVolumeSamplingNormalizer A k = 0 := by
  rw [complexVolumeSamplingNormalizer_eq_elementary]
  exact complexGramElementary_eq_zero_of_rank_lt A hk

omit [Fintype n] in
/-- The empty determinant has weight one, at every shape and rank.
Source: `sa:volume`, empty-sample convention. -/
@[simp] theorem complexVolumeSamplingWeight_empty (A : Matrix m n ℂ) :
    complexVolumeSamplingWeight A ∅ = 1 := by
  simp [complexVolumeSamplingWeight, Matrix.det_isEmpty]

/-- The size-zero normalizer equals one.
Source: `sa:volume`, empty-sample convention. -/
@[simp] theorem complexVolumeSamplingNormalizer_zero (A : Matrix m n ℂ) :
    complexVolumeSamplingNormalizer A 0 = 1 := by
  rw [complexVolumeSamplingNormalizer_eq_elementary, complexGramElementary_zero]

/-- Literal normalized complex volume probabilities, with zero mass off the
prescribed subset size. Feasibility is required by the normalization proof.
Source: `sa:volume`, actual finite subset algorithm. -/
def complexVolumeSamplingProbabilities (A : Matrix m n ℂ) (k : ℕ) : Finset n → ℝ≥0 :=
  fun S => if S.card = k then
    Real.toNNReal (complexVolumeSamplingWeight A S / complexVolumeSamplingNormalizer A k) else 0

/-- The actual prescribed-size probabilities sum to one precisely in the
proved positive-normalizer range. Source: `sa:volume`, actual law construction. -/
theorem sum_complexVolumeSamplingProbabilities (A : Matrix m n ℂ) {k : ℕ}
    (hk : k ≤ A.rank) : ∑ S, complexVolumeSamplingProbabilities A k S = 1 := by
  have hZ := (complexVolumeSamplingNormalizer_pos_iff A k).mpr hk
  apply NNReal.coe_injective
  rw [NNReal.coe_sum, NNReal.coe_one]
  simp only [complexVolumeSamplingProbabilities, apply_ite,
    Real.coe_toNNReal _ (div_nonneg (complexVolumeSamplingWeight_nonneg A _) hZ.le), NNReal.coe_zero]
  have hset : (Finset.univ : Finset (Finset n)).filter (fun S => S.card = k) =
      Finset.univ.powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, Finset.subset_univ]
  rw [← Finset.sum_filter, hset, ← Finset.sum_div]
  exact div_self hZ.ne'

/-- The actual complex volume-sampling PMF, defined only with a feasible
rank proof. Source: `sa:volume`, genuine normalized `k`-subset law. -/
def complexVolumeSamplingPMF (A : Matrix m n ℂ) {k : ℕ} (hk : k ≤ A.rank) : PMF (Finset n) :=
  finiteSamplingPMF (complexVolumeSamplingProbabilities A k)
    (sum_complexVolumeSamplingProbabilities A hk)

/-- The actual probability measure for determinant-weighted complex column
sampling. Source: `sa:volume`, genuine normalized finite subset law. -/
def complexVolumeSamplingLaw (A : Matrix m n ℂ) {k : ℕ} (hk : k ≤ A.rank) : Measure (Finset n) :=
  (complexVolumeSamplingPMF A hk).toMeasure

instance complexVolumeSamplingLaw_isProbabilityMeasure (A : Matrix m n ℂ)
    {k : ℕ} (hk : k ≤ A.rank) : IsProbabilityMeasure (complexVolumeSamplingLaw A hk) := by
  unfold complexVolumeSamplingLaw
  infer_instance

/-- Each actual outcome mass is its normalized Gram determinant, with zero
mass at every other cardinality. Source: `sa:volume`. -/
theorem complexVolumeSamplingLaw_singleton (A : Matrix m n ℂ) {k : ℕ}
    (hk : k ≤ A.rank) (S : Finset n) :
    (complexVolumeSamplingLaw A hk {S}).toReal =
      if S.card = k then complexVolumeSamplingWeight A S / complexVolumeSamplingNormalizer A k else 0 := by
  have hZ := (complexVolumeSamplingNormalizer_pos_iff A k).mpr hk
  rw [complexVolumeSamplingLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [complexVolumeSamplingPMF, finiteSamplingPMF, PMF.ofFintype_apply,
    ENNReal.coe_toReal, complexVolumeSamplingProbabilities, apply_ite,
    Real.coe_toNNReal _ (div_nonneg (complexVolumeSamplingWeight_nonneg A _) hZ.le), NNReal.coe_zero]
  split_ifs <;> rfl

/-- Real expectations under the actual complex subset law are precisely
the normalized prescribed-size weighted sum. Source: `sa:volume-theorem`. -/
theorem integral_complexVolumeSamplingLaw (A : Matrix m n ℂ) {k : ℕ}
    (hk : k ≤ A.rank) (f : Finset n → ℝ) :
    (∫ S, f S ∂complexVolumeSamplingLaw A hk) =
      ∑ S ∈ Finset.univ.powersetCard k,
        complexVolumeSamplingWeight A S / complexVolumeSamplingNormalizer A k * f S := by
  have hZ := (complexVolumeSamplingNormalizer_pos_iff A k).mpr hk
  rw [complexVolumeSamplingLaw, PMF.integral_eq_sum]
  simp only [complexVolumeSamplingPMF, finiteSamplingPMF, PMF.ofFintype_apply,
    ENNReal.coe_toReal, complexVolumeSamplingProbabilities, apply_ite,
    Real.coe_toNNReal _ (div_nonneg (complexVolumeSamplingWeight_nonneg A _) hZ.le),
    NNReal.coe_zero, smul_eq_mul, ite_mul, zero_mul]
  have hset : (Finset.univ : Finset (Finset n)).filter (fun S => S.card = k) =
      Finset.univ.powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, Finset.subset_univ]
  rw [← Finset.sum_filter, hset]

/-- Positive-probability outcomes have exactly the prescribed cardinality
and a positive complex Gram determinant. Source: `sa:volume`, true support. -/
theorem complexVolumeSamplingLaw_singleton_pos_iff (A : Matrix m n ℂ) {k : ℕ}
    (hk : k ≤ A.rank) (S : Finset n) :
    0 < (complexVolumeSamplingLaw A hk {S}).toReal ↔
      S.card = k ∧ 0 < complexVolumeSamplingWeight A S := by
  rw [complexVolumeSamplingLaw_singleton]
  have hZ := (complexVolumeSamplingNormalizer_pos_iff A k).mpr hk
  by_cases hS : S.card = k
  · simp only [hS, ite_true, true_and]
    exact div_pos_iff_of_pos_right hZ
  · simp only [hS, ite_false, lt_self_iff_false, false_and]

end NLAlib
