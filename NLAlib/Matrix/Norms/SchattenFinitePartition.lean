import NLAlib.Matrix.Norms.WithComplexSchatten
import NLAlib.ForMathlib.MeasureTheory.FiniteConditioningLp
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Finite-partition approximation for native complex Schatten moments

Explicit normalized atom integrals contract the actual matrix Schatten
moments. Conversely, a uniform bound for every finite partition passes to
the actual matrix-valued random variable by simple-function `L^p` density.
The formulas use ordinary complex matrices and the native Schatten norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators Matrix ENNReal

namespace NLAlib

variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

open scoped Matrix.Norms.L2Operator in
/-- Explicit atom averages contract an actual complex Schatten moment.
The Schatten and moment orders may be any separate real exponents at least
one. Zero-mass atoms use the normalized integral convention zero. -/
theorem sum_mul_schattenNormReal_finitePartitionMean_rpow_le_integral
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (cell : Ω → ι) (hcell : Measurable cell)
    {f : Ω → Matrix n n ℂ} (hf : Integrable f μ)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hfm : Integrable (fun ω => schattenNormReal (f ω) p ^ q) μ) :
    (∑ i, μ.real (cell ⁻¹' {i}) *
      schattenNormReal (finitePartitionMean μ cell f i) p ^ q) ≤
        ∫ ω, schattenNormReal (f ω) p ^ q ∂μ := by
  let T : Matrix n n ℂ →L[ℝ] WithComplexSchatten p hp n :=
    WithComplexSchatten.matrixContinuousLinearEquiv.toContinuousLinearMap
  have h := sum_mul_norm_finitePartitionMean_rpow_le_integral cell hcell (f := T ∘ f)
    (T.integrable_comp hf) hq (by exact hfm)
  simp_rw [finitePartitionMean_comp_continuousLinearMap cell hf T] at h
  exact h

open scoped Matrix.Norms.L2Operator in
/-- A uniform native Schatten moment bound for every finite measurable
partition implies the same bound for the actual complex matrix law. The
only integrability premise is membership of the actual matrix map in its
ordinary finite `L^p`, which is invariant under these equivalent norms. -/
theorem integral_schattenNormReal_rpow_root_le_of_finitePartitionMean_le
    {p : ℝ} (hp : 1 ≤ p) {f : Ω → Matrix n n ℂ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (C : ℝ) (hC : 0 ≤ C)
    (hfinite : ∀ (k : ℕ) (cell : Ω → Fin k), Measurable cell →
      (∑ i, μ.real (cell ⁻¹' {i}) *
        schattenNormReal (finitePartitionMean μ cell f i) p ^ p) ^ p⁻¹ ≤ C) :
    (∫ ω, schattenNormReal (f ω) p ^ p ∂μ) ^ p⁻¹ ≤ C := by
  let T : Matrix n n ℂ →L[ℝ] WithComplexSchatten p hp n :=
    WithComplexSchatten.matrixContinuousLinearEquiv.toContinuousLinearMap
  have hF : MemLp (T ∘ f) (ENNReal.ofReal p) μ := hf.continuousLinearMap_comp T
  have h := integral_norm_rpow_root_le_of_finitePartitionMean_le hp (f := T ∘ f) hF C hC ?_
  · exact h
  · intro k cell hcell
    simp_rw [finitePartitionMean_comp_continuousLinearMap cell
      (hf.integrable (by simpa using ENNReal.ofReal_le_ofReal hp)) T]
    exact hfinite k cell hcell

end NLAlib
