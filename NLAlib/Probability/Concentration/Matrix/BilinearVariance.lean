import NLAlib.ForMathlib.Probability.ComplexSecondMoment
import NLAlib.ForMathlib.Analysis.Matrix.BilinearFunctional
import NLAlib.Matrix.Norms.BilinearProbes

/-!
# Actual bilinear variance of an independent matrix sum

The source sigma-star geometry is the squared complex modulus of a genuine
probe of the centered full sum. Independence and zero means identify this
quantity with the sum of the marginal probe second moments used in the
checked empirical-process estimate.

Source: arXiv:2201.05142v3, Theorem 2.6 and Section 5.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

/-- The native complex second moment of a probe of an actual independent
centered matrix sum equals the sum of its marginal probe second moments.
The probes are arbitrary, not just coordinate vectors or equal vectors.
atlas: independent-sum-spectrum-universality (partial) -/
theorem integral_norm_sq_bilinear_sum_pi_eq_sum
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (a b : EuclideanSpace ℂ n) :
    (∫ x : ι → Ω, ‖star a.ofLp ⬝ᵥ ((∑ i, Z i (x i)) *ᵥ b.ofLp)‖ ^ 2 ∂Measure.pi ν) =
      ∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖ ^ 2 ∂ν i := by
  let : SecondCountableTopology (Matrix n n ℂ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  let L := Matrix.bilinearCLM a.ofLp b.ofLp
  have hZi (i : ι) : MemLp (Z i) 2 (ν i) :=
    MemLp.of_bound (hZm i).aestronglyMeasurable R (hZ i)
  have hLi (i : ι) : MemLp (fun ω => L (Z i ω)) 2 (ν i) := by
    simpa only [Function.comp_def] using L.comp_memLp' (hZi i)
  have hLm (i : ι) : ∫ ω, L (Z i ω) ∂ν i = 0 := by
    rw [L.integral_comp_comm ((hZi i).integrable one_le_two), hmean i, map_zero]
  have h := integral_norm_sq_sum_pi_of_mean_zero ν (fun i ω => L (Z i ω)) hLi hLm
  change (∫ x : ι → Ω, ‖L (∑ i, Z i (x i))‖ ^ 2 ∂Measure.pi ν) =
    ∑ i, ∫ ω, ‖L (Z i ω)‖ ^ 2 ∂ν i
  simpa only [map_sum] using h

end NLAlib
