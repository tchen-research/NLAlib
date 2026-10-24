import NLAlib.ForMathlib.LinearAlgebra.Matrix.PrincipalMinorExpansion
import NLAlib.Matrix.Inequalities.PrincipalMinorProducts
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.HasLaw

/-!
# Variable-size determinantal L-ensembles

PSD principal-minor weights define an actual finite PMF and probability
measure, without a rank or nonsingularity condition on the kernel. Their
multivariate generating function is the normalized determinant.
Source: Dereziński–Mahoney 2020, §3, Definitions 2–4.
Atlas: `l-ensemble-law`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The L-ensemble normalizer is the sum of every principal minor, including
the empty minor one. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-law (partial) -/
theorem sum_principalMinor_eq_det_one_add (L : Matrix n n ℝ) :
    ∑ S : Finset n, principalMinor L S = (1 + L).det := by
  exact (Matrix.det_one_add_eq_sum_principal_minors L).symm

/-- The L-ensemble normalizer is at least one, even for a singular or zero
PSD kernel and in dimension zero. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-law (partial) -/
theorem one_le_det_one_add_of_posSemidef {L : Matrix n n ℝ} (hL : L.PosSemidef) :
    1 ≤ (1 + L).det := by
  classical
  rw [← sum_principalMinor_eq_det_one_add]
  have h := Finset.single_le_sum (fun S (_ : S ∈ (Finset.univ : Finset (Finset n))) =>
    principalMinor_nonneg hL S) (Finset.mem_univ (∅ : Finset n))
  simpa only [principalMinor, Matrix.toBlock, Matrix.det_isEmpty] using h

/-- The normalized principal-minor mass. For kernels outside the PSD domain
this is merely a total scalar formula; `lEnsemblePMF` requires PSD. -/
def lEnsembleProbability (L : Matrix n n ℝ) (S : Finset n) : ℝ :=
  principalMinor L S / (1 + L).det

/-- Each L-ensemble mass is nonnegative for a PSD kernel. -/
theorem lEnsembleProbability_nonneg {L : Matrix n n ℝ} (hL : L.PosSemidef)
    (S : Finset n) : 0 ≤ lEnsembleProbability L S :=
  div_nonneg (principalMinor_nonneg hL S) ((by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_det_one_add_of_posSemidef hL))

/-- All L-ensemble masses sum to one. No prescribed cardinality is imposed. -/
theorem sum_lEnsembleProbability {L : Matrix n n ℝ} (hL : L.PosSemidef) :
    ∑ S : Finset n, lEnsembleProbability L S = 1 := by
  simp only [lEnsembleProbability, ← Finset.sum_div, sum_principalMinor_eq_det_one_add]
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one
    (one_le_det_one_add_of_posSemidef hL)))

/-- The variable-size determinantal PMF on every finite subset of the index
set. The empty determinant has mass `1 / det (I + L)`.
Dereziński–Mahoney 2020, §3, Definition 3.
atlas: l-ensemble-law (partial) -/
def lEnsemblePMF (L : Matrix n n ℝ) (hL : L.PosSemidef) : PMF (Finset n) := by
  classical
  refine PMF.ofFintype (fun S => ENNReal.ofReal (lEnsembleProbability L S)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => lEnsembleProbability_nonneg hL S),
    sum_lEnsembleProbability hL]
  simp

/-- The variable-size L-ensemble probability measure associated with a real
PSD kernel. Dereziński–Mahoney 2020, §3, Definition 3.
atlas: l-ensemble-law (partial) -/
def lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef) : Measure (Finset n) :=
  (lEnsemblePMF L hL).toMeasure

/-- The normalized principal-minor measure is a probability measure. -/
instance lEnsembleLaw_isProbabilityMeasure (L : Matrix n n ℝ) (hL : L.PosSemidef) :
    IsProbabilityMeasure (lEnsembleLaw L hL) := by
  unfold lEnsembleLaw
  infer_instance

/-- The L-ensemble assigns total mass one to all finite subsets.
Dereziński–Mahoney 2020, §3, Definition 3.
atlas: l-ensemble-law (partial) -/
theorem lEnsembleLaw_univ (L : Matrix n n ℝ) (hL : L.PosSemidef) :
    lEnsembleLaw L hL Set.univ = 1 := measure_univ

/-- Expectations under an L-ensemble are finite sums of its principal-minor
probabilities. Every function on this finite sample space is integrable. -/
theorem integral_lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef)
    (f : Finset n → ℝ) :
    ∫ S, f S ∂lEnsembleLaw L hL = ∑ S, lEnsembleProbability L S * f S := by
  classical
  rw [lEnsembleLaw, PMF.integral_eq_sum]
  simp only [lEnsemblePMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (lEnsembleProbability_nonneg hL _), smul_eq_mul]

/-- The mass of each finite subset is exactly its normalized principal minor.
Dereziński–Mahoney 2020, §3, Definition 3.
atlas: l-ensemble-law (partial) -/
theorem lEnsembleLaw_singleton (L : Matrix n n ℝ) (hL : L.PosSemidef) (S : Finset n) :
    (lEnsembleLaw L hL).real {S} = lEnsembleProbability L S := by
  classical
  rw [Measure.real, lEnsembleLaw,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton S)]
  simp only [lEnsemblePMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (lEnsembleProbability_nonneg hL S)]

/-- The L-ensemble generating function is the normalized multivariate
principal-minor determinant, for arbitrary real row weights including negative
and zero weights. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-law (partial) -/
theorem integral_prod_lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef) (z : n → ℝ) :
    ∫ S, (∏ i ∈ S, z i) ∂lEnsembleLaw L hL =
      (1 + Matrix.diagonal z * L).det / (1 + L).det := by
  rw [integral_lEnsembleLaw, Matrix.det_one_add_diagonal_mul]
  simp only [lEnsembleProbability, principalMinor, Matrix.toBlock, div_mul_eq_mul_div,
    Finset.sum_div]

/-- The same generating-function identity holds for any random finite subset
with the L-ensemble law. -/
theorem integral_prod_lEnsembleLaw_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (L : Matrix n n ℝ) (hL : L.PosSemidef)
    {S : Ω → Finset n} (hS : HasLaw S (lEnsembleLaw L hL) μ) (z : n → ℝ) :
    ∫ ω, (∏ i ∈ S ω, z i) ∂μ =
      (1 + Matrix.diagonal z * L).det / (1 + L).det := by
  have hm : AEStronglyMeasurable (fun T : Finset n => ∏ i ∈ T, z i)
      (lEnsembleLaw L hL) := (measurable_of_finite _).aestronglyMeasurable
  exact (hS.integral_comp hm).trans (integral_prod_lEnsembleLaw L hL z)

end NLAlib
