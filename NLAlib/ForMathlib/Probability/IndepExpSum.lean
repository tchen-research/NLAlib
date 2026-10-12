import Mathlib.Probability.Moments.Basic

/-!
# Exponential integrability of independent sums, a.e.-measurable version

`iIndepFun.integrable_exp_mul_sum₀`: the `AEMeasurable` version of Mathlib's
`ProbabilityTheory.iIndepFun.integrable_exp_mul_sum` (which needs `Measurable` summands).
Candidate for `Mathlib/Probability/Moments/Basic.lean`.

Moved from the Hanson–Wright proof (ported from HighDimProb commit c0cb8d9) in the dedup round
(2026-10-12).
-/

open MeasureTheory ProbabilityTheory Real

namespace NLAlib

/-- If the `X i` are independent and a.e.-measurable and each `exp (t X i)` is integrable for
`i ∈ s`, then `exp (t ∑_{i ∈ s} X i)` is integrable; the `AEMeasurable` version of
`iIndepFun.integrable_exp_mul_sum`. Atlas `hanson-wright` (helper). -/
theorem iIndepFun.integrable_exp_mul_sum₀ {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Finset ι} {t : ℝ}
    (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    Integrable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi_notin_s h_rec =>
      have h_int_s : ∀ j ∈ s, Integrable (fun ω : Ω => exp (t * X j ω)) μ :=
        fun j hj => h_int j (Finset.mem_insert_of_mem hj)
      specialize h_rec h_int_s
      rw [Finset.sum_insert hi_notin_s]
      refine IndepFun.integrable_exp_mul_add ?_ (h_int i (Finset.mem_insert_self _ _)) h_rec
      exact (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi_notin_s).symm

end NLAlib
