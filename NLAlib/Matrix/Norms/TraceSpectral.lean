import Mathlib.Analysis.Normed.Module.FiniteDimension
import NLAlib.Matrix.Norms.EntryBounds
import NLAlib.Matrix.Norms.TraceNuclear

/-!
# The spectral norm bounds the normalized trace

The coordinate estimate includes every finite dimension, with normalized
trace equal to zero in the empty case.
-/

noncomputable section
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The trace norm is at most the matrix dimension times the spectral norm. -/
theorem norm_trace_le_card_mul_specNorm (A : Matrix n n 𝕜) :
    ‖A.trace‖ ≤ Fintype.card n * specNorm A := by
  calc
    ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, specNorm A := Finset.sum_le_sum fun i _ => norm_apply_le_specNorm A i i
    _ = _ := by simp

/-- Dimension-normalized trace is bounded by the spectral norm, including
empty matrices. -/
theorem norm_normalizedTrace_le_specNorm (A : Matrix n n 𝕜) :
    ‖normalizedTrace A‖ ≤ specNorm A := by
  rw [norm_normalizedTrace]
  by_cases h : Fintype.card n = 0
  · simp [h,specNorm_nonneg]
  · have hd : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
    exact (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using norm_trace_le_card_mul_specNorm A)

open scoped Matrix.Norms.L2Operator in
/-- Dimension-normalized trace is a contractive continuous linear observation
for the matrix spectral norm, including empty matrices. -/
theorem norm_toContinuousLinearMap_normalizedTraceLinearMap_le_one :
    ‖(normalizedTraceLinearMap : Matrix n n 𝕜 →ₗ[𝕜] 𝕜).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  simpa only [LinearMap.coe_toContinuousLinearMap', normalizedTraceLinearMap_apply,
    one_mul, specNorm_eq_norm] using norm_normalizedTrace_le_specNorm A

end NLAlib
