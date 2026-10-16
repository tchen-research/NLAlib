import NLAlib.Matrix.Spectral.EigenvectorSpectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix

/-! # Peripheral eigenvalues of convergent matrix powers

A unit-modulus scalar whose powers converge must equal one. Applying a
convergent matrix power sequence to an eigenvector transfers this rigidity
to every peripheral eigenvalue, without a diagonalizability hypothesis.
Source: Horn–Johnson, Matrix Analysis, §5.6.
-/
noncomputable section
open Filter
open scoped Matrix Topology
namespace Complex

/-- A convergent power sequence on the complex unit circle is constant at one. -/
theorem eq_one_of_tendsto_pow_of_norm_eq_one {z a : ℂ} (hz : ‖z‖ = 1)
    (ha : Tendsto (fun k : ℕ => z ^ k) atTop (𝓝 a)) : z = 1 := by
  have hnorm : ‖a‖ = 1 := tendsto_nhds_unique ha.norm (by
    simpa only [norm_pow, hz, one_pow] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have hane : a ≠ 0 := by intro h; simp [h] at hnorm
  have hshift := ha.comp (tendsto_add_atTop_nat 1)
  have hmul : Tendsto (fun k : ℕ => z ^ (k + 1)) atTop (𝓝 (z * a)) := by
    simpa only [pow_succ'] using ha.const_mul z
  have heq := tendsto_nhds_unique hmul hshift
  exact mul_right_cancel₀ hane (by simpa only [one_mul] using heq)

end Complex

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every unit-modulus spectral value of a matrix with convergent powers is one.
Source: Horn–Johnson, §5.6.
atlas: primitive-perron-power-limit (partial) -/
theorem eigenvalue_eq_one_of_tendsto_pow {T L : Matrix ι ι ℂ}
    (hlim : Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 L))
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ T) (hμnorm : ‖μ‖ = 1) : μ = 1 := by
  obtain ⟨z, hz, he⟩ := NLAlib.exists_mulVec_eq_smul_of_mem_spectrum hμ
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
  have hc : Continuous (fun M : Matrix ι ι ℂ => (M *ᵥ z) j / z j) := by fun_prop
  have hp : Tendsto (fun k : ℕ => μ ^ k) atTop (𝓝 ((L *ᵥ z) j / z j)) := by
    convert hc.continuousAt.tendsto.comp hlim using 1
    funext k
    change μ ^ k = (T ^ k *ᵥ z) j / z j
    rw [pow_mulVec_eq_pow_smul_of_mulVec_eq_smul he, Pi.smul_apply, smul_eq_mul,
      mul_div_cancel_right₀ _ hj]
  exact Complex.eq_one_of_tendsto_pow_of_norm_eq_one hμnorm hp

end Matrix
