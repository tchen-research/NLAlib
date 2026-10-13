import NLAlib.Matrix.Structured.Measurable
/-!
# Measurable spectral projection residuals

Entrywise measurability suffices for the spectral norm and for projection residuals,
through the product σ-algebra `Matrix.instMeasurableSpace`.
-/

noncomputable section
open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace NLAlib

/-- Entrywise measurable matrix maps have measurable spectral norms. Source:
finite-dimensional norm continuity; HMT (2011), expected-error integration helpers. -/
theorem measurable_specNorm_of_entries {γ m n : Type*} [MeasurableSpace γ]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {f : γ → Matrix m n ℝ} (hf : ∀ i j, Measurable fun z => f z i j) :
    Measurable fun z => specNorm (f z) := by
  exact continuous_norm.measurable.comp (Matrix.measurable_iff_entries.mpr hf)

/-- A projection residual has measurable spectral norm for an entrywise measurable
frame. Source: HMT (2011), Theorems 10.6--10.7, measurability step. -/
theorem measurable_specNorm_residual_of {γ m n q : Type*} [MeasurableSpace γ]
    [Fintype m] [Fintype n] [Fintype q] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) {Q : γ → Matrix m q ℝ}
    (hQ : ∀ i j, Measurable fun z => Q z i j) :
    Measurable fun z => specNorm (projResidual (Q z) A) := by
  apply measurable_specNorm_of_entries
  intro i j
  simp only [projResidual, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.sub_apply,
      Matrix.mul_apply,
    Matrix.transpose_apply]
  fun_prop

end NLAlib
