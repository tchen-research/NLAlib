import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.RCLike.Basic

/-!
# Measurability of the total matrix inverse

The native matrix inverse is determinant reciprocal times adjugate, so it is
measurable even at singular matrices where the total inverse is zero.
-/

noncomputable section

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  [SecondCountableTopology 𝕜]
  [Fintype n] [DecidableEq n]

/-- The native total inverse of finite real or complex matrices is measurable,
including at singular matrices. -/
theorem measurable_inv : Measurable (fun A : Matrix n n 𝕜 => A⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (continuous_id.matrix_det.measurable.inv).smul
    continuous_id.matrix_adjugate.measurable

end Matrix
