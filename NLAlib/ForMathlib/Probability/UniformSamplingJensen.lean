import NLAlib.ForMathlib.Probability.UniformSamplingCounts

/-!
# Actual without-replacement versus iid convex-order comparison

The support-extension coupling's computed conditional barycenter, finite
Jensen, and its genuine marginals prove Hoeffding's finite comparison.
Source: operator re-derivation `sh:convex-sampling`; supports `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical ENNReal
namespace NLAlib

/-- The actual uniform PMF on literal exact-size row subsets.
Source: operator re-derivation `sh:convex-sampling`. -/
def uniformExactRowSubsetPMF {α : Type*} [Fintype α] {k : ℕ}
    (hk : k ≤ Fintype.card α) : PMF (ExactRowSubset α k) := by
  have := exactRowSubset_nonempty hk
  exact PMF.uniformOfFintype _

/-- Every exact-size subset has exactly the finite uniform probability mass.
Source: operator re-derivation `sh:convex-sampling`. -/
theorem uniformExactRowSubsetPMF_toReal_apply
    {α : Type*} [Fintype α] {k : ℕ} (hk : k ≤ Fintype.card α) (T : ExactRowSubset α k) :
    (uniformExactRowSubsetPMF hk T).toReal = 1 / (Fintype.card (ExactRowSubset α k) : ℝ) := by
  simp [uniformExactRowSubsetPMF, PMF.uniformOfFintype_apply, one_div]

/-- The actual coupling conditional weights average to the iid uniform
sequence masses. Source: operator re-derivation `sh:convex-sampling`. -/
theorem sum_uniformSubset_mul_conditionalWeight
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (I : Fin k → α) :
    (∑ T : ExactRowSubset α k, (1 / (Fintype.card (ExactRowSubset α k) : ℝ)) *
      iidSubsetConditionalWeight hk T I) = 1 / (Fintype.card (Fin k → α) : ℝ) := by
  obtain ⟨T0⟩ := exactRowSubset_nonempty hk
  have hN : (Fintype.card (ExactRowSubset α k) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨T0⟩ : 0 < Fintype.card (ExactRowSubset α k)).ne'
  simp only [iidSubsetConditionalWeight]
  simp_rw [← mul_assoc, one_div_mul_cancel hN, one_mul]
  exact iidSubsetJointPMF_toReal_first_marginal hk I

/-- The literal uniform exact-subset sum is below the iid uniform sequence
sum in convex order. All probability masses and conditional barycenters are
derived from the explicit support-extension coupling; repeated population
values are permitted because their labels remain distinct.
Source: Hoeffding 1963; operator re-derivation `sh:convex-sampling`. -/
theorem uniform_subset_average_convex_le_iid
    {α E : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [AddCommGroup E] [Module ℝ E]
    {k : ℕ} (hk0 : 0 < k) (hk : k ≤ Fintype.card α) (A : α → E) (f : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f) :
    (∑ T : ExactRowSubset α k, (1 / (Fintype.card (ExactRowSubset α k) : ℝ)) *
      f (∑ j ∈ T.val, A j)) ≤
      ∑ I : Fin k → α, (1 / (Fintype.card (Fin k → α) : ℝ)) * f (∑ a, A (I a)) := by
  have hJensen : ∀ T : ExactRowSubset α k,
      f (∑ j ∈ T.val, A j) ≤ ∑ I : Fin k → α,
        iidSubsetConditionalWeight hk T I * f (∑ a, A (I a)) := by
    intro T
    have hh := hf.map_sum_le (t := Finset.univ)
      (w := iidSubsetConditionalWeight hk T)
      (fun I _ => iidSubsetConditionalWeight_nonneg hk T I)
      (sum_iidSubsetConditionalWeight hk T)
      (fun (I : Fin k → α) _ => Set.mem_univ (∑ a, A (I a)))
    rw [sum_conditionalWeight_smul_sequence_sum hk0 hk T A] at hh
    simpa only [smul_eq_mul] using hh
  calc
    _ ≤ ∑ T : ExactRowSubset α k, (1 / (Fintype.card (ExactRowSubset α k) : ℝ)) *
        ∑ I : Fin k → α, iidSubsetConditionalWeight hk T I * f (∑ a, A (I a)) :=
      Finset.sum_le_sum (fun T _ => mul_le_mul_of_nonneg_left (hJensen T) (by positivity))
    _ = ∑ I : Fin k → α,
        (∑ T : ExactRowSubset α k, (1 / (Fintype.card (ExactRowSubset α k) : ℝ)) *
          iidSubsetConditionalWeight hk T I) * f (∑ a, A (I a)) := by
      simp only [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by simp_rw [sum_uniformSubset_mul_conditionalWeight]

/-- Actual uniform probability measures satisfy the finite convex-order
comparison for iid sampling and sampling without replacement.
Source: operator re-derivation `sh:convex-sampling`; Bochner expectation form. -/
theorem integral_uniform_subset_convex_le_iid
    {α E : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [AddCommGroup E] [Module ℝ E] {k : ℕ}
    [MeasurableSpace (ExactRowSubset α k)] [MeasurableSingletonClass (ExactRowSubset α k)]
    (hk0 : 0 < k) (hk : k ≤ Fintype.card α) (A : α → E) (f : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f) :
    (∫ T, f (∑ j ∈ T.val, A j) ∂(uniformExactRowSubsetPMF hk).toMeasure) ≤
      ∫ I : Fin k → α, f (∑ a, A (I a)) ∂(PMF.uniformOfFintype (Fin k → α)).toMeasure := by
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp only [uniformExactRowSubsetPMF_toReal_apply, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, one_div]
  simpa only [one_div] using uniform_subset_average_convex_le_iid hk0 hk A f hf

end NLAlib
