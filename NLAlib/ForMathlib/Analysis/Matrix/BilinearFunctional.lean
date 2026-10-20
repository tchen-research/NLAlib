import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous matrix bilinear probes

Evaluation between two fixed vectors is a continuous linear functional of
the matrix in its native Euclidean operator norm. This interface lets such
probes commute with actual Bochner expectations.
-/

noncomputable section
set_option autoImplicit false

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- The continuous linear functional evaluating a matrix between fixed probes. -/
def bilinearCLM (v : m → 𝕜) (w : n → 𝕜) : Matrix m n 𝕜 →L[𝕜] 𝕜 :=
  ({ toFun := fun A => star v ⬝ᵥ (A *ᵥ w)
     map_add' := by intro A B; simp [Matrix.add_mulVec, dotProduct_add]
     map_smul' := by intro c A; simp [Matrix.smul_mulVec, dotProduct_smul] } :
    Matrix m n 𝕜 →ₗ[𝕜] 𝕜).toContinuousLinearMap

/-- The bundled functional is exactly the native matrix bilinear expression. -/
@[simp] theorem bilinearCLM_apply (v : m → 𝕜) (w : n → 𝕜) (A : Matrix m n 𝕜) :
    bilinearCLM v w A = star v ⬝ᵥ (A *ᵥ w) := rfl

end Matrix
