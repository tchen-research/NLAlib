import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.RCLike.Basic

/-!
# Normalized trace

The dimension-normalized trace uses the reciprocal of the dimension, with
value zero for the empty index type. Algebraic identities hold uniformly;
normalization of the identity requires a positive dimension.
-/

noncomputable section
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- The dimension-normalized matrix trace. It is zero on empty matrices. -/
def normalizedTrace (A : Matrix n n 𝕜) : 𝕜 := (Fintype.card n : 𝕜)⁻¹ * A.trace

/-- Normalized trace is linear over the scalar field. -/
def normalizedTraceLinearMap : Matrix n n 𝕜 →ₗ[𝕜] 𝕜 :=
  (Fintype.card n : 𝕜)⁻¹ • Matrix.traceLinearMap n 𝕜 𝕜

/-- Evaluation of the normalized trace linear map. -/
@[simp] theorem normalizedTraceLinearMap_apply (A : Matrix n n 𝕜) :
    normalizedTraceLinearMap A = normalizedTrace A := rfl

/-- Normalized trace preserves sums. -/
@[simp] theorem normalizedTrace_add (A B : Matrix n n 𝕜) :
    normalizedTrace (A+B) = normalizedTrace A + normalizedTrace B :=
  normalizedTraceLinearMap.map_add A B

/-- Normalized trace preserves scalar multiplication. -/
@[simp] theorem normalizedTrace_smul (c : 𝕜) (A : Matrix n n 𝕜) :
    normalizedTrace (c • A) = c * normalizedTrace A :=
  normalizedTraceLinearMap.map_smul c A

/-- The normalized trace of zero is zero. -/
@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : Matrix n n 𝕜) = 0 :=
  normalizedTraceLinearMap.map_zero

/-- Normalized trace preserves differences. -/
@[simp] theorem normalizedTrace_sub (A B : Matrix n n 𝕜) :
    normalizedTrace (A-B) = normalizedTrace A - normalizedTrace B :=
  normalizedTraceLinearMap.map_sub A B

/-- Normalized trace is cyclic on square matrix products. -/
theorem normalizedTrace_mul_comm (A B : Matrix n n 𝕜) :
    normalizedTrace (A*B) = normalizedTrace (B*A) := by
  simp only [normalizedTrace,Matrix.trace_mul_comm A B]

/-- The normalized trace of the identity is one in positive dimension. -/
@[simp] theorem normalizedTrace_one [DecidableEq n] [Nonempty n] :
    normalizedTrace (1 : Matrix n n 𝕜) = 1 := by
  simp [normalizedTrace,Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

end NLAlib
