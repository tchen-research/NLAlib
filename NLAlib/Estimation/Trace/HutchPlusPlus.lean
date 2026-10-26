import NLAlib.Estimation.Trace.Unbiased
import NLAlib.Matrix.Subspaces.RangeProjector
import NLAlib.Matrix.Measurability.GramPseudoinverse

/-!
# Canonical-projector formulas for the native Hutch++ estimator

The rank-adaptive basis in `hutchPlusPlusEstimate` yields the measurable canonical range
projector. All scalar estimator identities therefore hold across rank drops without assuming
that an arbitrary basis choice is measurable.
Source: Meyer–Musco–Musco–Woodruff (2021), Algorithm 1; the projector route in the supplied
estimation derivations, §1.1. Related proof source: NLA-lib/NLAlib, HutchPlusPlus.lean.
-/

noncomputable section
open scoped Matrix
open Matrix MeasureTheory

namespace NLAlib

variable {n s r : Type*} [Fintype n] [Fintype s] [Fintype r]
  [DecidableEq n] [DecidableEq s] [DecidableEq r]

omit [DecidableEq s] in
/-- The chosen sketch-range basis gives the canonical range projector, even at rank drops. -/
theorem hutchPlusPlusBasis_mul_transpose_eq_rangeProjector
    (A : Matrix n n ℝ) (S : Matrix n s ℝ) :
    hutchPlusPlusBasis A S * (hutchPlusPlusBasis A S)ᵀ = rangeProjector (A * S) := by
  exact (rangeProjector_eq_mul_conjTranspose_of_range_eq
    (hasOrthonormalCols_hutchPlusPlusBasis A S) (range_hutchPlusPlusBasis A S).symm).symm

/-- The two-sided compression of `A` to the complement of its sampled range. -/
def hutchPlusPlusResidual (A : Matrix n n ℝ) (S : Matrix n s ℝ) : Matrix n n ℝ :=
  (1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))

omit [DecidableEq s] [DecidableEq r] in
/-- The native basis-defined Hutch++ estimator equals its canonical-projector formula. -/
theorem hutchPlusPlusEstimate_eq_projector (A : Matrix n n ℝ)
    (S : Matrix n s ℝ) (Z : Matrix n r ℝ) :
    hutchPlusPlusEstimate A S Z = (A * rangeProjector (A * S)).trace +
      hutchinsonEstimate (hutchPlusPlusResidual A S) Z := by
  unfold hutchPlusPlusEstimate deflatedTraceEstimate
  rw [hutchPlusPlusBasis_mul_transpose_eq_rangeProjector]
  congr 1
  rw [Matrix.trace_mul_cycle, hutchPlusPlusBasis_mul_transpose_eq_rangeProjector,
    Matrix.trace_mul_comm]

omit [DecidableEq s] in
/-- The trace is the sum of the sampled-range trace and the complementary residual trace. -/
theorem trace_eq_trace_mul_rangeProjector_add_trace_hutchPlusPlusResidual
    (A : Matrix n n ℝ) (S : Matrix n s ℝ) :
    A.trace = (A * rangeProjector (A * S)).trace + (hutchPlusPlusResidual A S).trace := by
  have h := trace_eq_trace_mul_mul_add_trace_sub_mul_mul_sub
    (rangeProjector_mul_self (A * S)) A
  rw [Matrix.trace_mul_cycle, rangeProjector_mul_self, Matrix.trace_mul_comm] at h
  exact h

omit [DecidableEq s] [DecidableEq r] in
/-- The entire Hutch++ error is the Hutchinson error of the complementary residual. -/
theorem hutchPlusPlusEstimate_sub_trace (A : Matrix n n ℝ)
    (S : Matrix n s ℝ) (Z : Matrix n r ℝ) :
    hutchPlusPlusEstimate A S Z - A.trace =
      hutchinsonEstimate (hutchPlusPlusResidual A S) Z - (hutchPlusPlusResidual A S).trace := by
  rw [hutchPlusPlusEstimate_eq_projector,
    trace_eq_trace_mul_rangeProjector_add_trace_hutchPlusPlusResidual A S]
  ring

/-- The compressed residual is measurable as a function of the entire range sketch. -/
theorem measurable_hutchPlusPlusResidual (A : Matrix n n ℝ) :
    Measurable (hutchPlusPlusResidual A : Matrix n s ℝ → Matrix n n ℝ) := by
  have hP := measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_id
    : Measurable (fun S : Matrix n s ℝ => A * S))
  have hPe := Matrix.measurable_iff_entries.mp hP
  apply Matrix.measurable_iff_entries.mpr
  intro i j
  simp only [hutchPlusPlusResidual, Matrix.mul_apply, Matrix.sub_apply]
  fun_prop

omit [DecidableEq r] in
/-- The native Hutch++ scalar estimate is jointly measurable in the range sketch and probes;
no measurability assumption on the chosen orthonormal basis is needed. -/
theorem measurable_hutchPlusPlusEstimate (A : Matrix n n ℝ) :
    Measurable (fun p : Matrix n s ℝ × Matrix n r ℝ => hutchPlusPlusEstimate A p.1 p.2) := by
  simp_rw [hutchPlusPlusEstimate_eq_projector]
  have hP := measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_fst
    : Measurable (fun p : Matrix n s ℝ × Matrix n r ℝ => A * p.1))
  have hC : Measurable (fun p : Matrix n s ℝ × Matrix n r ℝ => hutchPlusPlusResidual A p.1) :=
    (measurable_hutchPlusPlusResidual A).comp measurable_fst
  have htrace : Measurable (fun p : Matrix n s ℝ × Matrix n r ℝ =>
      (A * rangeProjector (A * p.1)).trace) := by
    simp only [Matrix.trace]
    fun_prop
  refine htrace.add ?_
  simp only [hutchinsonEstimate, quadForm_eq_sum, star_trivial]
  fun_prop

end NLAlib
