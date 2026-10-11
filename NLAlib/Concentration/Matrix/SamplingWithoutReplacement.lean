import NLAlib.ForMathlib.Probability.UniformSamplingJensen
import NLAlib.ForMathlib.Probability.UniformProduct
import NLAlib.Concentration.Matrix.OperatorConvexity.TraceExpConvex
import NLAlib.Concentration.Matrix.Chernoff.ChernoffMgfCgf
import NLAlib.Concentration.Matrix.Laplace.TraceCgfSubadditivity
import NLAlib.Concentration.Matrix.OperatorConvexity.TraceExpMonotone
import NLAlib.Concentration.Matrix.Sampling
import Mathlib.Probability.Independence.InfinitePi

/-!
# Matrix Chernoff for actual sampling without replacement

The trace exponential comparison uses the proved finite coupling, and the
iid trace MGF uses the proved matrix cumulant theorem. Source: operator
re-derivation `sh:convex-sampling` and `sh:srht-ose`; atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory
open scoped Classical Matrix Matrix.Norms.L2Operator ENNReal ComplexOrder
namespace NLAlib

/-- The trace exponential of a scalar identity has its exact scalar value.
Source: the spectral formula; supports `sh:srht-ose`. -/
theorem traceExp_smul_one {d : ℕ} [NeZero d] (t : ℝ) :
    traceExp (t • (1 : Matrix (Fin d) (Fin d) ℂ)) = d * Real.exp t := by
  have hI := (Matrix.isHermitian_one : (1 : Matrix (Fin d) (Fin d) ℂ).IsHermitian)
  rw [traceExp_smul_eq_sum _ hI]
  have he (i : Fin d) : hI.eigenvalues i = 1 := by
    have hi := hI.eigenvalues_mem_spectrum_real i
    simpa only [spectrum.one_eq, Set.mem_singleton_iff] using hi
  simp only [he, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- Convexity of the actual trace exponential on bundled Hermitian matrices,
at either sign of the Laplace parameter. Source: `sh:convex-sampling`. -/
theorem convexOn_traceExp_smul_selfAdjoint {d : ℕ} [NeZero d] (θ : ℝ) :
    ConvexOn ℝ Set.univ
      (fun A : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) => traceExp (θ • A.val)) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb hab
  have hA : (θ • A.val).IsHermitian :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr selfAdjoint.isSelfAdjoint).smul (IsSelfAdjoint.all θ)
  have hB : (θ • B.val).IsHermitian :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr selfAdjoint.isSelfAdjoint).smul (IsSelfAdjoint.all θ)
  have hh := (convexOn_traceExp_isHermitian (d := d)).2 hA hB ha hb hab
  simpa only [selfAdjoint.val_smul, AddSubgroup.coe_add, smul_add, smul_smul,
    mul_comm θ] using hh

/-- The genuine uniform-subset trace MGF is below the uniform-iid trace MGF.
Source: Hoeffding comparison from the explicit support-extension coupling. -/
theorem integral_traceExp_uniform_subset_le_iid
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {d k : ℕ} [NeZero d]
    (hk0 : 0 < k) (hk : k ≤ Fintype.card α)
    (A : α → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ j, (A j).IsHermitian) (θ : ℝ) :
    (∫ T, traceExp (θ • ∑ j ∈ T.val, A j) ∂(uniformExactRowSubsetPMF hk).toMeasure) ≤
      ∫ I : Fin k → α, traceExp (θ • ∑ a, A (I a))
        ∂(PMF.uniformOfFintype (Fin k → α)).toMeasure := by
  let B : α → selfAdjoint (Matrix (Fin d) (Fin d) ℂ) := fun j => ⟨A j, hA j⟩
  have hh := integral_uniform_subset_convex_le_iid hk0 hk B
    (fun M => traceExp (θ • M.val)) (convexOn_traceExp_smul_selfAdjoint θ)
  have hs (s : Finset α) : (↑(∑ j ∈ s, B j) : Matrix (Fin d) (Fin d) ℂ) = ∑ j ∈ s, A j := by
    exact (map_sum (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)).subtype (fun j => B j) s)
  have hi (I : Fin k → α) : (↑(∑ a, B (I a)) : Matrix (Fin d) (Fin d) ℂ) = ∑ a, A (I a) := by
    exact (map_sum (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)).subtype (fun a => B (I a)) Finset.univ)
  simpa only [hs, hi] using hh

/-- The actual iid uniform sequence trace MGF under bounded PSD population
atoms with mean identity. Every dependence and mean condition is derived
from the actual finite law. Source: `sh:srht-ose` Chernoff step. -/
theorem integral_traceExp_uniform_iid_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {d k : ℕ} [NeZero d]
    (A : α → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hA : ∀ j, (A j).IsHermitian)
    (hbound : ∀ j, 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L)
    (hmean : (1 / (Fintype.card α : ℝ)) • ∑ j, A j = 1) (θ : ℝ) :
    (∫ I : Fin k → α, traceExp (θ • ∑ a, A (I a))
      ∂(PMF.uniformOfFintype (Fin k → α)).toMeasure) ≤
      d * Real.exp ((k : ℝ) * chernoffCgfCoefficient L θ) := by
  let μ := (PMF.uniformOfFintype (Fin k → α)).toMeasure
  let X : Fin k → (Fin k → α) → Matrix (Fin d) (Fin d) ℂ := fun a I => A (I a)
  have hm (a : Fin k) : Measurable (X a) := Measurable.of_discrete
  have hh (a : Fin k) : ∀ᵐ I ∂μ, (X a I).IsHermitian :=
    Filter.Eventually.of_forall (fun I => hA (I a))
  have hb (a : Fin k) : ∀ᵐ I ∂μ,
      0 ≤ lambdaMin (X a I) ∧ lambdaMax (X a I) ≤ L :=
    Filter.Eventually.of_forall (fun I => hbound (I a))
  have hi : iIndepFun X μ := by
    rw [show μ = Measure.pi (fun _ : Fin k => (PMF.uniformOfFintype α).toMeasure)
      from uniform_function_toMeasure_eq_pi (ι := Fin k) (α := α)]
    change iIndepFun (fun a (I : Fin k → α) => A (I a))
      (Measure.pi (fun _ : Fin k => (PMF.uniformOfFintype α).toMeasure))
    exact iIndepFun_pi (μ := fun _ : Fin k => (PMF.uniformOfFintype α).toMeasure)
      (X := fun _ : Fin k => A)
      (fun _ => (show Measurable A from .of_discrete).aemeasurable)
  have he (a : Fin k) : ∫ I, X a I ∂μ = 1 := by
    rw [show μ = Measure.pi (fun _ : Fin k => (PMF.uniformOfFintype α).toMeasure)
      from uniform_function_toMeasure_eq_pi (ι := Fin k) (α := α)]
    have hev := (measurePreserving_eval (fun _ : Fin k =>
      (PMF.uniformOfFintype α).toMeasure) a).map_eq
    have hmap := integral_map
      (μ := Measure.pi (fun _ : Fin k => (PMF.uniformOfFintype α).toMeasure))
      (φ := fun I : Fin k → α => I a) (f := A)
      (measurable_pi_apply a).aemeasurable Measurable.of_discrete.aestronglyMeasurable
    change (∫ I, A (I a) ∂Measure.pi (fun _ : Fin k =>
      (PMF.uniformOfFintype α).toMeasure)) = 1
    rw [← hmap, hev, PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ← Finset.smul_sum]
    simpa only [one_div] using hmean
  have hexp (a : Fin k) : Integrable (fun I => matrixExp (θ • X a I)) μ :=
    Integrable.of_finite
  have hcum := trace_cgf_subadditivity μ X θ hm hh hi hexp
  have hcH : (cumulantSum μ X θ).IsHermitian :=
    isSelfAdjoint_sum _ (fun a _ => cfc_predicate Real.log _)
  have hsum : LoewnerLE (cumulantSum μ X θ)
      (((k : ℝ) * chernoffCgfCoefficient L θ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    have hc (a : Fin k) :=
      (chernoff_matrix_mgf_cgf_le μ (X a) L hL (hm a) (hh a) (hb a) θ).2
    have hs : LoewnerLE (cumulantSum μ X θ)
        (∑ _a : Fin k, chernoffCgfCoefficient L θ • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
      unfold LoewnerLE cumulantSum
      rw [← Finset.sum_sub_distrib]
      exact Matrix.posSemidef_sum _ (fun a _ => by simpa only [he, LoewnerLE] using hc a)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul] using hs
  calc
    _ ≤ traceExp (cumulantSum μ X θ) := by
      simpa only [X, Finset.smul_sum] using hcum
    _ ≤ traceExp (((k : ℝ) * chernoffCgfCoefficient L θ) •
        (1 : Matrix (Fin d) (Fin d) ℂ)) :=
      traceExp_le_traceExp _ _ hcH (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)) hsum
    _ = _ := traceExp_smul_one _

end NLAlib
