import NLAlib.Probability.Moments.MatrixDifference
import NLAlib.Probability.Moments.Schatten
import NLAlib.Probability.Exchangeable.ThirdCopyMoments
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Actual laws and resampling averages of matrix difference moments

Pushing independent summand laws through a real linear map gives their actual
matrix third difference moment. The genuine common-index resampling triple
has each of its three differences' normalized cubic moments equal to M3/N.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {ι E n : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype n] [DecidableEq n] [Nonempty n]

open scoped Matrix.Norms.L2Operator in
/-- Independent pushforwards preserve the actual same-law-copy moment formula. -/
theorem matrixDifferenceThirdMoment_map
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (T : E → Matrix n n ℂ) (hT : Measurable T) :
    matrixDifferenceThirdMoment (fun i => (ν i).map T) =
      ∑ i, ∫ p : E × E, schattenNormReal (T p.1 - T p.2) 3 ^ 3 /
        (Fintype.card n : ℝ) ∂(ν i).prod (ν i) := by
  unfold matrixDifferenceThirdMoment
  apply Finset.sum_congr rfl
  intro i hi
  have hm : MeasurePreserving T (ν i) ((ν i).map T) := ⟨hT,rfl⟩
  have htest : Measurable (fun p : Matrix n n ℂ × Matrix n n ℂ =>
      schattenNormReal (p.1-p.2) 3 ^ 3 / (Fintype.card n : ℝ)) :=
    ((((continuous_schattenNormReal (by norm_num : (0 : ℝ) < 3)).comp
      (continuous_fst.sub continuous_snd)).pow 3).div_const _).measurable
  simpa only [Function.comp_def,Prod.map_fst,Prod.map_snd] using
    ((hm.prod hm).hasLaw.integral_comp htest.aestronglyMeasurable).symm

open scoped Matrix.Norms.L2Operator in
/-- A real linear map can be applied to the copy difference before taking
its actual normalized Schatten cubic moment. -/
theorem matrixDifferenceThirdMoment_map_continuousLinearMap
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (T : E →L[ℝ] Matrix n n ℂ) :
    matrixDifferenceThirdMoment (fun i => (ν i).map T) =
      ∑ i, ∫ p : E × E, schattenNormReal (T (p.1-p.2)) 3 ^ 3 /
        (Fintype.card n : ℝ) ∂(ν i).prod (ν i) := by
  simpa only [map_sub] using matrixDifferenceThirdMoment_map ν T T.continuous.measurable

open scoped Matrix.Norms.L2Operator in
/-- Actual third matrix moments of independent-copy differences are integrable
whenever the original summand law has a third norm moment. -/
theorem integrable_schattenNormReal_linear_copy_difference_pow_three
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : MemLp (id : E → E) 3 ν)
    (T : E →L[ℝ] Matrix n n ℂ) :
    Integrable (fun p : E × E => schattenNormReal (T (p.1-p.2)) 3 ^ 3 /
      (Fintype.card n : ℝ)) (ν.prod ν) := by
  have hf : MemLp (fun p : E × E => p.1) 3 (ν.prod ν) :=
    hν.comp_measurePreserving (measurePreserving_fst (μ := ν) (ν := ν))
  have hs : MemLp (fun p : E × E => p.2) 3 (ν.prod ν) :=
    hν.comp_measurePreserving (measurePreserving_snd (μ := ν) (ν := ν))
  have hT : MemLp (fun p : E × E => T (p.1-p.2)) 3 (ν.prod ν) :=
    T.comp_memLp' (hf.sub hs)
  exact (integrable_schattenNormReal_pow_of_memLp _ hT (by norm_num : (3 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) < 3)).div_const _

open scoped Matrix.Norms.L2Operator in
/-- The transformed moment sum is nonnegative under actual probability laws. -/
theorem matrixDifferenceThirdMoment_map_nonneg
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (T : E →L[ℝ] Matrix n n ℂ) :
    0 ≤ matrixDifferenceThirdMoment (fun i => (ν i).map T) := by
  rw [matrixDifferenceThirdMoment_map_continuousLinearMap]
  apply Finset.sum_nonneg
  intro i hi
  exact integral_nonneg fun p => div_nonneg
    (pow_nonneg (schattenNormReal_nonneg _ _) _) (Nat.cast_nonneg _)

variable [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

open scoped Matrix.Norms.L2Operator in
/-- Every selected pair of distinct copies has the exact transformed normalized
third moment M3/N. This is a genuine expectation on the actual triple law. -/
theorem integral_schattenNormReal_resamplingTriple_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 3 (ν i)) (T : E →L[ℝ] Matrix n n ℂ)
    (a b : Fin 3) (hab : a ≠ b) :
    (∫ p : ι × ((ι × Fin 3) → E),
      schattenNormReal (T (p.2 (p.1,a)-p.2 (p.1,b))) 3 ^ 3 / (Fintype.card n : ℝ)
      ∂resamplingTripleMeasure ν) =
      matrixDifferenceThirdMoment (fun i => (ν i).map T) / (Fintype.card ι : ℝ) := by
  let G : E → ℝ := fun x => schattenNormReal (T x) 3 ^ 3 / (Fintype.card n : ℝ)
  have hG : Measurable G :=
    ((((continuous_schattenNormReal (by norm_num : (0 : ℝ) < 3)).comp T.continuous).pow 3).div_const _).measurable
  have hi (i : ι) : Integrable (fun p : E × E => G (p.1-p.2)) ((ν i).prod (ν i)) :=
    integrable_schattenNormReal_linear_copy_difference_pow_three (ν i) (hν i) T
  calc
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ p : E × E, G (p.1-p.2) ∂(ν i).prod (ν i) :=
      integral_resamplingTriple_selected_difference ν a b hab G hG hi
    _ = _ := by rw [matrixDifferenceThirdMoment_map_continuousLinearMap]; dsimp [G]; ring

open scoped Matrix.Norms.L2Operator in
/-- The transformed cubic test of any selected copy difference is genuinely
integrable; finite third moments of the summands are sufficient. -/
theorem integrable_schattenNormReal_resamplingTriple_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 3 (ν i)) (T : E →L[ℝ] Matrix n n ℂ)
    (a b : Fin 3) (hab : a ≠ b) :
    Integrable (fun p : ι × ((ι × Fin 3) → E) =>
      schattenNormReal (T (p.2 (p.1,a)-p.2 (p.1,b))) 3 ^ 3 / (Fintype.card n : ℝ))
      (resamplingTripleMeasure ν) := by
  refine integrable_resamplingTriple_selected_difference ν a b hab
    (fun x => schattenNormReal (T x) 3 ^ 3 / (Fintype.card n : ℝ)) ?_ ?_
  · exact ((((continuous_schattenNormReal (by norm_num : (0 : ℝ) < 3)).comp
      T.continuous).pow 3).div_const _).measurable
  · intro i
    exact integrable_schattenNormReal_linear_copy_difference_pow_three (ν i) (hν i) T

variable {Z : Type*} [MeasurableSpace Z]

open scoped Matrix.Norms.L2Operator in
/-- Adjoining an arbitrary independent probability sample preserves genuine
integrability of every transformed selected-copy cubic moment. -/
theorem integrable_schattenNormReal_resamplingTriple_prod_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 3 (ν i)) (T : E →L[ℝ] Matrix n n ℂ)
    (γ : Measure Z) [IsProbabilityMeasure γ] (a b : Fin 3) (hab : a ≠ b) :
    Integrable (fun q : (ι × ((ι × Fin 3) → E)) × Z =>
      schattenNormReal (T (q.1.2 (q.1.1,a)-q.1.2 (q.1.1,b))) 3 ^ 3 /
        (Fintype.card n : ℝ)) ((resamplingTripleMeasure ν).prod γ) :=
  (integrable_schattenNormReal_resamplingTriple_selected_difference ν hν T a b hab).comp_fst γ

open scoped Matrix.Norms.L2Operator in
/-- The common transformed cubic moment remains M3/N after adjoining any
independent probability sample to the actual resampling triple. -/
theorem integral_schattenNormReal_resamplingTriple_prod_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 3 (ν i)) (T : E →L[ℝ] Matrix n n ℂ)
    (γ : Measure Z) [IsProbabilityMeasure γ] (a b : Fin 3) (hab : a ≠ b) :
    (∫ q : (ι × ((ι × Fin 3) → E)) × Z,
      schattenNormReal (T (q.1.2 (q.1.1,a)-q.1.2 (q.1.1,b))) 3 ^ 3 /
        (Fintype.card n : ℝ) ∂(resamplingTripleMeasure ν).prod γ) =
      matrixDifferenceThirdMoment (fun i => (ν i).map T) / (Fintype.card ι : ℝ) := by
  let G : (ι × ((ι × Fin 3) → E)) → ℝ := fun p =>
    schattenNormReal (T (p.2 (p.1,a)-p.2 (p.1,b))) 3 ^ 3 / (Fintype.card n : ℝ)
  change (∫ q, G q.1 ∂(resamplingTripleMeasure ν).prod γ) = _
  rw [integral_fun_fst (μ := resamplingTripleMeasure ν) (ν := γ) G]
  simp only [probReal_univ,one_smul]
  exact integral_schattenNormReal_resamplingTriple_selected_difference ν hν T a b hab

open scoped Matrix.Norms.L2Operator in
/-- All three actual resampling differences have genuine normalized Schatten
cubic integrability on the triple times an independent probability space.
The linear reconstruction is arbitrary and the summand laws may differ.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integrable_schattenNormReal_resamplingTriple_prod_differences
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 3 (ν i)) (T : E →L[ℝ] Matrix n n ℂ)
    (γ : Measure Z) [IsProbabilityMeasure γ] :
    Integrable (fun q : (ι × ((ι × Fin 3) → E)) × Z =>
      schattenNormReal (T (resamplingTripleOriginal q.1-resamplingTripleFirst q.1)) 3 ^ 3 /
        (Fintype.card n : ℝ)) ((resamplingTripleMeasure ν).prod γ) ∧
    Integrable (fun q : (ι × ((ι × Fin 3) → E)) × Z =>
      schattenNormReal (T (resamplingTripleFirst q.1-resamplingTripleSecond q.1)) 3 ^ 3 /
        (Fintype.card n : ℝ)) ((resamplingTripleMeasure ν).prod γ) ∧
    Integrable (fun q : (ι × ((ι × Fin 3) → E)) × Z =>
      schattenNormReal (T (resamplingTripleOriginal q.1-resamplingTripleSecond q.1)) 3 ^ 3 /
        (Fintype.card n : ℝ)) ((resamplingTripleMeasure ν).prod γ) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [resamplingTriple_difference] using
      integrable_schattenNormReal_resamplingTriple_prod_selected_difference ν hν T γ 0 1 (by decide)
  · simpa only [resamplingTriple_first_sub_second] using
      integrable_schattenNormReal_resamplingTriple_prod_selected_difference ν hν T γ 1 2 (by decide)
  · simpa only [resamplingTriple_difference_second] using
      integrable_schattenNormReal_resamplingTriple_prod_selected_difference ν hν T γ 0 2 (by decide)

open scoped Matrix.Norms.L2Operator in
/-- The normalized cubic moments of all three actual transformed resampling
differences are the same actual M3/N on the full product space. L3 summands
derive integrability, so these equalities never rely on Bochner junk values.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_schattenNormReal_resamplingTriple_prod_differences
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 3 (ν i)) (T : E →L[ℝ] Matrix n n ℂ)
    (γ : Measure Z) [IsProbabilityMeasure γ] :
    ((∫ q : (ι × ((ι × Fin 3) → E)) × Z,
      schattenNormReal (T (resamplingTripleOriginal q.1-resamplingTripleFirst q.1)) 3 ^ 3 /
        (Fintype.card n : ℝ) ∂(resamplingTripleMeasure ν).prod γ) =
      matrixDifferenceThirdMoment (fun i => (ν i).map T) / (Fintype.card ι : ℝ)) ∧
    ((∫ q : (ι × ((ι × Fin 3) → E)) × Z,
      schattenNormReal (T (resamplingTripleFirst q.1-resamplingTripleSecond q.1)) 3 ^ 3 /
        (Fintype.card n : ℝ) ∂(resamplingTripleMeasure ν).prod γ) =
      matrixDifferenceThirdMoment (fun i => (ν i).map T) / (Fintype.card ι : ℝ)) ∧
    ((∫ q : (ι × ((ι × Fin 3) → E)) × Z,
      schattenNormReal (T (resamplingTripleOriginal q.1-resamplingTripleSecond q.1)) 3 ^ 3 /
        (Fintype.card n : ℝ) ∂(resamplingTripleMeasure ν).prod γ) =
      matrixDifferenceThirdMoment (fun i => (ν i).map T) / (Fintype.card ι : ℝ)) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [resamplingTriple_difference] using
      integral_schattenNormReal_resamplingTriple_prod_selected_difference ν hν T γ 0 1 (by decide)
  · simpa only [resamplingTriple_first_sub_second] using
      integral_schattenNormReal_resamplingTriple_prod_selected_difference ν hν T γ 1 2 (by decide)
  · simpa only [resamplingTriple_difference_second] using
      integral_schattenNormReal_resamplingTriple_prod_selected_difference ν hν T γ 0 2 (by decide)

end NLAlib
