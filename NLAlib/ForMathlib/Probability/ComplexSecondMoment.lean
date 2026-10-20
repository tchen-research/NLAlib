import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Second moments of centered independent complex sums

The squared modulus of a genuine centered complex sum has expectation
equal to the sum of the marginal squared-modulus expectations. The proof
uses the native real and imaginary variance identities, retaining full
complex bilinear variance geometry in matrix applications.
-/

noncomputable section
set_option autoImplicit false
open ProbabilityTheory

namespace MeasureTheory

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

private theorem integral_sq_sum_pi_of_mean_zero
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 (ν i))
    (hmean : ∀ i, ∫ ω, X i ω ∂ν i = 0) :
    (∫ x : ι → Ω, (∑ i, X i (x i)) ^ 2 ∂Measure.pi ν) =
      ∑ i, ∫ ω, X i ω ^ 2 ∂ν i := by
  have hXi (i : ι) : Integrable (fun x : ι → Ω => X i (x i)) (Measure.pi ν) :=
    (measurePreserving_eval ν i).integrable_comp_of_integrable ((hX i).integrable one_le_two)
  have hL : MemLp (fun x : ι → Ω => ∑ i, X i (x i)) 2 (Measure.pi ν) :=
    memLp_finsetSum Finset.univ fun i _ => (hX i).comp_measurePreserving (measurePreserving_eval ν i)
  have hm : (∫ x : ι → Ω, ∑ i, X i (x i) ∂Measure.pi ν) = 0 := by
    rw [integral_finsetSum _ (fun i _ => hXi i)]
    simp only [integral_comp_eval (μ := ν) (i := _) (hX _).aestronglyMeasurable, hmean,
      Finset.sum_const_zero]
  have h := variance_sum_pi hX
  have he : (∑ i, fun x : ι → Ω => X i (x i)) = (fun x => ∑ i, X i (x i)) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he, variance_eq_sub hL, hm] at h
  simp_rw [variance_eq_sub (hX _), hmean] at h
  simpa only [Pi.pow_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using h

/-- The actual squared modulus of a centered independent complex sum has
expectation equal to the sum of its actual marginal second moments. The
laws may be singular and the summand family may be empty. -/
theorem integral_norm_sq_sum_pi_of_mean_zero
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (X : ι → Ω → ℂ) (hX : ∀ i, MemLp (X i) 2 (ν i))
    (hmean : ∀ i, ∫ ω, X i ω ∂ν i = 0) :
    (∫ x : ι → Ω, ‖∑ i, X i (x i)‖ ^ 2 ∂Measure.pi ν) =
      ∑ i, ∫ ω, ‖X i ω‖ ^ 2 ∂ν i := by
  let R (i : ι) (ω : Ω) := (X i ω).re
  let I (i : ι) (ω : Ω) := (X i ω).im
  have hR (i : ι) : MemLp (R i) 2 (ν i) := by
    simpa only [RCLike.re_eq_complex_re] using (hX i).re
  have hI (i : ι) : MemLp (I i) 2 (ν i) := by
    simpa only [RCLike.im_eq_complex_im] using (hX i).im
  have hmR (i : ι) : ∫ ω, R i ω ∂ν i = 0 := by
    simpa only [Complex.reCLM_apply, map_zero] using
      (Complex.reCLM.integral_comp_comm ((hX i).integrable one_le_two)).trans
        (congrArg Complex.reCLM (hmean i))
  have hmI (i : ι) : ∫ ω, I i ω ∂ν i = 0 := by
    simpa only [Complex.imCLM_apply, map_zero] using
      (Complex.imCLM.integral_comp_comm ((hX i).integrable one_le_two)).trans
        (congrArg Complex.imCLM (hmean i))
  have hSr : MemLp (fun x : ι → Ω => ∑ i, R i (x i)) 2 (Measure.pi ν) :=
    memLp_finsetSum Finset.univ fun i _ => (hR i).comp_measurePreserving (measurePreserving_eval ν i)
  have hSi : MemLp (fun x : ι → Ω => ∑ i, I i (x i)) 2 (Measure.pi ν) :=
    memLp_finsetSum Finset.univ fun i _ => (hI i).comp_measurePreserving (measurePreserving_eval ν i)
  have hnorm (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    have h := Complex.sq_norm_sub_sq_re z
    linarith
  calc
    _ = (∫ x : ι → Ω, (∑ i, R i (x i)) ^ 2 ∂Measure.pi ν) +
        ∫ x : ι → Ω, (∑ i, I i (x i)) ^ 2 ∂Measure.pi ν := by
      simp_rw [hnorm, Complex.re_sum, Complex.im_sum]
      exact integral_add hSr.integrable_sq hSi.integrable_sq
    _ = (∑ i, ∫ ω, R i ω ^ 2 ∂ν i) + ∑ i, ∫ ω, I i ω ^ 2 ∂ν i := by
      rw [integral_sq_sum_pi_of_mean_zero ν R hR hmR,
        integral_sq_sum_pi_of_mean_zero ν I hI hmI]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← integral_add (hR i).integrable_sq (hI i).integrable_sq]
      apply integral_congr_ae
      exact ae_of_all _ fun ω => (hnorm (X i ω)).symm

end MeasureTheory
