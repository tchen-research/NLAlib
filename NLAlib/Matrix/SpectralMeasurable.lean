import NLAlib.Matrix.Measurable
import NLAlib.Matrix.Spectral

/-!
# Measurable spectral projection residuals

Entrywise measurability suffices for the spectral norm and for projection residuals.
This avoids a global measurable-space instance for real matrices.
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
  have h1 : Measurable fun z => Matrix.of.symm (f z) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hf i j
  have h2 : Continuous (fun M : m → n → ℝ => ‖Matrix.of M‖) :=
    continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

/-- A projection residual has measurable spectral norm for an entrywise measurable
frame. Source: HMT (2011), Theorems 10.6--10.7, measurability step. -/
theorem measurable_specNorm_residual_of {γ m n q : Type*} [MeasurableSpace γ]
    [Fintype m] [Fintype n] [Fintype q] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) {Q : γ → Matrix m q ℝ}
    (hQ : ∀ i j, Measurable fun z => Q z i j) :
    Measurable fun z => specNorm (residual (Q z) A) := by
  apply measurable_specNorm_of_entries
  intro i j
  simp only [residual, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

end NLAlib
