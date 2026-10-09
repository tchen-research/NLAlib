import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import NLAlib.Matrix.Norms

/-!
# Subspace embeddings

`NLAlib.IsSubspaceEmbedding S U ε`: the sketch `S` preserves every squared norm on the column
space of `U` to within `1 ± ε`. Stated for an arbitrary spanning matrix `U` (not necessarily
orthonormal); with `U` orthonormal it is equivalent to `σ(SU) ⊂ [√(1−ε), √(1+ε)]`, which is a
planned lemma. Oblivious embeddings are a property of a law on sketches and are stated per
distribution (`gaussian-ose`, `srht-ose`, …).

Atlas: `ose-def`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {k m d : Type*} [Fintype k] [Fintype m] [Fintype d]

/-- `S` is an `ε`-subspace embedding for `range U`. -/
def IsSubspaceEmbedding (S : Matrix k m ℝ) (U : Matrix m d ℝ) (ε : ℝ) : Prop :=
  ∀ x : d → ℝ,
    (1 - ε) * ((U *ᵥ x) ⬝ᵥ (U *ᵥ x)) ≤ (S *ᵥ (U *ᵥ x)) ⬝ᵥ (S *ᵥ (U *ᵥ x)) ∧
    (S *ᵥ (U *ᵥ x)) ⬝ᵥ (S *ᵥ (U *ᵥ x)) ≤ (1 + ε) * ((U *ᵥ x) ⬝ᵥ (U *ᵥ x))

end NLAlib
