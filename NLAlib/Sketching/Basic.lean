import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Subspace embeddings

`NLAlib.IsSubspaceEmbedding S U ε`: the sketch `S` preserves every squared norm on the column
space of `U` to within `1 ± ε`. Stated for an arbitrary spanning matrix `U` (not necessarily
orthonormal). Oblivious embeddings are a property of a law on sketches and are stated per
distribution (`gaussian-ose`, `srht-ose`, …). The equivalent forms and basic properties are in
`NLAlib.Sketching.SubspaceEmbedding`.

Atlas: `ose-def` (definition).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {k m d : Type*} [Fintype k] [Fintype m] [Fintype d]

/-- `S` is an `ε`-subspace embedding for `range U`: `(1 - ε)‖Ux‖² ≤ ‖SUx‖² ≤ (1 + ε)‖Ux‖²` for
every `x`. Woodruff 2014 §2.1; Martinsson–Tropp 2020 §8.7. Atlas: `ose-def`. -/
def IsSubspaceEmbedding (S : Matrix k m ℝ) (U : Matrix m d ℝ) (ε : ℝ) : Prop :=
  ∀ x : d → ℝ,
    (1 - ε) * ((U *ᵥ x) ⬝ᵥ (U *ᵥ x)) ≤ (S *ᵥ (U *ᵥ x)) ⬝ᵥ (S *ᵥ (U *ᵥ x)) ∧
    (S *ᵥ (U *ᵥ x)) ⬝ᵥ (S *ᵥ (U *ᵥ x)) ≤ (1 + ε) * ((U *ᵥ x) ⬝ᵥ (U *ᵥ x))

end NLAlib
