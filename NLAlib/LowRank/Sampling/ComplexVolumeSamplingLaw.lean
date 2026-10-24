import NLAlib.Matrix.Subspaces.ComplexVolumeProjection
import NLAlib.Probability.Sampling.FiniteSampling
import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Spectral.PrincipalMinors
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
/-!
# Actual complex determinant-weighted subset law

Nonnegative complex Gram determinants define a literal finite probability
law exactly at feasible ranks. No zero normalizer is used to manufacture a
law above the input rank. Source: `sa:volume`; atlas `volume-sampling`.
-/

noncomputable section
open MeasureTheory
open scoped Classical Matrix ComplexOrder NNReal ENNReal
namespace NLAlib

/-! ### Complex Gram spectrum and volume normalizers

The genuine complex Gram spectrum identifies the fixed-order principal-minor
normalizer with an elementary symmetric sum. Its positivity is exactly the
rank condition, including zero rank and empty index types. (Moved here from
`Matrix/Spectral/ComplexVolumeSpectrum` by foundation change F1; this file is its only
direct consumer.) -/

section ComplexGramSpectrum

open Polynomial
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The sorted, nonnegative eigenvalues of the actual complex column Gram
matrix. Source: the Hermitian spectral theorem; manuscript `sa:volume-theorem`. -/
def complexGramEigenvalues (A : Matrix m n ℂ) : Fin (Fintype.card n) → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀

/-- The elementary symmetric Gram spectral sum on the native column labels.
Source: the determinant normalizer in manuscript `sa:volume-theorem`. -/
def complexGramElementary (A : Matrix m n ℂ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k,
    ∏ i ∈ S, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i

/-- The sorted Gram spectral tail after removing `k` eigenvalues. Source:
Frobenius Eckart–Young; manuscript `sa:volume-theorem`. -/
def complexGramTail (A : Matrix m n ℂ) (k : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card n), if k ≤ (i : ℕ) then complexGramEigenvalues A i else 0

/-- Actual complex Gram eigenvalues are nonnegative. Source: positivity of
`AᴴA`; supports manuscript `sa:volume-theorem`. -/
theorem complexGramEigenvalues_nonneg (A : Matrix m n ℂ)
    (i : Fin (Fintype.card n)) : 0 ≤ complexGramEigenvalues A i := by
  have h := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A
    (Fintype.equivOfCardEq (Fintype.card_fin _) i)
  simpa [Matrix.IsHermitian.eigenvalues, complexGramEigenvalues] using h

/-- The actual complex Gram eigenvalues are in decreasing order. Source:
Mathlib's sorted Hermitian spectrum; supports `sa:volume-theorem`. -/
theorem complexGramEigenvalues_antitone (A : Matrix m n ℂ) :
    Antitone (complexGramEigenvalues A) :=
  (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀_antitone

/-- A nonnegative elementary symmetric sum is positive exactly when at least
`k` weights are nonzero. Source: the positive-support argument in the
volume-sampling normalizer, manuscript `sa:volume-theorem`. -/
theorem sum_powersetCard_prod_pos_iff_card_nonzero {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (k : ℕ) :
    0 < (∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, a i) ↔
      k ≤ Fintype.card {i // a i ≠ 0} := by
  classical
  let T := Finset.univ.filter fun i => a i ≠ 0
  have hcard : T.card = Fintype.card {i // a i ≠ 0} := by
    simp [T, Fintype.card_subtype]
  rw [← hcard]
  constructor
  · intro h
    obtain ⟨S, hS, hp⟩ :=
      (Finset.sum_pos_iff_of_nonneg fun S _ => Finset.prod_nonneg fun i _ => ha i).mp h
    have hST : S ⊆ T := by
      intro i hi
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hz => (ne_of_gt hp) (Finset.prod_eq_zero hi hz)
    exact (Finset.mem_powersetCard.mp hS).2.symm ▸ Finset.card_le_card hST
  · intro hk
    obtain ⟨S, hST, hSk⟩ := Finset.exists_subset_card_eq hk
    apply (Finset.sum_pos_iff_of_nonneg fun S _ =>
      Finset.prod_nonneg fun i _ => ha i).mpr
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hSk⟩, ?_⟩
    apply Finset.prod_pos
    intro i hi
    have hne : a i ≠ 0 := (Finset.mem_filter.mp (hST hi)).2
    exact lt_of_le_of_ne (ha i) (Ne.symm hne)

/-- The actual complex volume spectral normalizer is positive exactly at
feasible ranks, including rank zero. Source: manuscript `sa:volume-theorem`.
atlas: volume-sampling (partial) -/
theorem complexGramElementary_pos_iff (A : Matrix m n ℂ) (k : ℕ) :
    0 < complexGramElementary A k ↔ k ≤ A.rank := by
  rw [complexGramElementary, sum_powersetCard_prod_pos_iff_card_nonzero
    _ (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A)]
  rw [← (Matrix.isHermitian_conjTranspose_mul_self A).rank_eq_card_non_zero_eigs,
    Matrix.rank_conjTranspose_mul_self]

/-- Elementary Gram sums are nonnegative. Source: Gram positivity;
supports the probability normalizer of manuscript `sa:volume-theorem`. -/
theorem complexGramElementary_nonneg (A : Matrix m n ℂ) (k : ℕ) :
    0 ≤ complexGramElementary A k := by
  exact Finset.sum_nonneg fun S _ => Finset.prod_nonneg fun i _ =>
    Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i

/-- Infeasible ranks have zero complex volume normalizer. Source: the rank
condition in manuscript `sa:volume-theorem`. -/
theorem complexGramElementary_eq_zero_of_rank_lt (A : Matrix m n ℂ) {k : ℕ}
    (hk : A.rank < k) : complexGramElementary A k = 0 := by
  exact le_antisymm (not_lt.mp (by
    simpa [complexGramElementary_pos_iff] using not_le.mpr hk))
    (complexGramElementary_nonneg A k)

/-- The order-zero spectral normalizer equals one for every complex matrix.
Source: the empty determinant convention in manuscript `sa:volume-theorem`. -/
@[simp] theorem complexGramElementary_zero (A : Matrix m n ℂ) :
    complexGramElementary A 0 = 1 := by simp [complexGramElementary]

/-- The real complex Gram principal-minor normalizer equals its actual
elementary spectral sum. Source: manuscript `sa:volume-theorem`.
atlas: volume-sampling (partial) -/
theorem sum_re_det_complex_gram_principal_minors_eq (A : Matrix m n ℂ) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, ((Aᴴ * A).submatrix
      (Subtype.val : S → n) (Subtype.val : S → n)).det.re) =
      complexGramElementary A k := by
  have h := congrArg Complex.re
    (Matrix.IsHermitian.sum_det_principal_minors_eq_sum_prod
      (Matrix.isHermitian_conjTranspose_mul_self A) k)
  simpa [complexGramElementary, ← Complex.ofReal_prod] using h

/-- Elementary spectral sums commute with relabeling by an equivalence.
Source: finite spectral relabeling; supports `sa:volume-theorem`. -/
theorem sum_powersetCard_prod_eq_of_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (a : κ → ℝ) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, a i) =
      ∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, a (e i) := by
  rw [← Finset.map_univ_equiv e, Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro S _
  change (∏ i ∈ S.map e.toEmbedding, a i) = ∏ i ∈ S, a (e i)
  exact Finset.prod_map S e.toEmbedding a

/-- The native-index Gram normalizer equals the elementary sum of the sorted
Gram eigenvalues. Source: the spectral determinant proof in
manuscript `sa:volume-theorem`. -/
theorem complexGramElementary_eq_sum_prod_sorted (A : Matrix m n ℂ) (k : ℕ) :
    complexGramElementary A k =
      ∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card n))).powersetCard k,
        ∏ i ∈ S, complexGramEigenvalues A i := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [complexGramElementary, sum_powersetCard_prod_eq_of_equiv e]
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply,
    complexGramEigenvalues]

end ComplexGramSpectrum


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
  A - rangeProjector (complexVolumeSampleColumns A S) * A

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
