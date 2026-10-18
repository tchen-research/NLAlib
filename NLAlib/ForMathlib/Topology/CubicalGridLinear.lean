import NLAlib.ForMathlib.Topology.CubicalGrid
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Linear realization and support of actual finite grid chains

The horizontal and vertical coefficient arrays form an ordinary finite
integer module. Their realization as actual continuous grid edges is a
linear map, and its image has only the active canonical edges in its support.
-/

noncomputable section
open Finset
open scoped unitInterval
namespace Cubical.Grid

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] {m n : ℕ}

/-- The native pair of horizontal and vertical finite integer arrays. -/
abbrev Coefficients (m n : ℕ) :=
  (Fin m → Fin (n + 1) → ℤ) × (Fin (m + 1) → Fin n → ℤ)

/-- Realize the actual finite grid coefficient arrays as a signed native
continuous edge chain. -/
def edgeChainMap (v : Fin (m + 1) → Fin (n + 1) → E) :
    Coefficients m n →ₗ[ℤ] OneChain E where
  toFun c := edgeChain v c.1 c.2
  map_add' a b := by
    simp only [edgeChain, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, sum_add_distrib]
    abel
  map_smul' k a := by
    simp only [edgeChain, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_smul,
      smul_add, smul_sum, smul_eq_mul, RingHom.id_apply]

/-- Every active canonical edge in a prescribed set gives an actual grid
chain in the corresponding native supported submodule. This also transports
edge properties, such as smoothness, independently of pointwise containment. -/
theorem edgeChain_mem_supported
    (v : Fin (m + 1) → Fin (n + 1) → E)
    (h : Fin m → Fin (n + 1) → ℤ) (w : Fin (m + 1) → Fin n → ℤ)
    (S : Set C(I, E))
    (hH : ∀ i j, h i j ≠ 0 → horizontal v i j ∈ S)
    (hV : ∀ i j, w i j ≠ 0 → vertical v i j ∈ S) :
    edgeChain v h w ∈ Finsupp.supported ℤ ℤ S := by
  classical
  let P := Finsupp.supported ℤ ℤ S
  apply P.add_mem
  · apply P.sum_mem
    intro i _
    apply P.sum_mem
    intro j _
    by_cases hc : h i j = 0
    · simpa only [hc, zero_smul] using P.zero_mem
    · exact P.smul_mem _ (Finsupp.single_mem_supported ℤ 1 (hH i j hc))
  · apply P.sum_mem
    intro i _
    apply P.sum_mem
    intro j _
    by_cases hc : w i j = 0
    · simpa only [hc, zero_smul] using P.zero_mem
    · exact P.smul_mem _ (Finsupp.single_mem_supported ℤ 1 (hV i j hc))

end Cubical.Grid
