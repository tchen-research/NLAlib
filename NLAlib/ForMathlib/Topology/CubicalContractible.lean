import NLAlib.ForMathlib.Topology.CubicalMaps
import Mathlib.Topology.Homotopy.Contractible

/-! # Finite cubical cycles in contractible spaces

Apply an actual contraction to each active continuous edge. Its two endpoint
faces are the contraction paths of the endpoints, so they cancel exactly
when the finite endpoint boundary is zero. This constructs finite normalized
two-chain fillings without joining the edges into one parameterized loop.
-/

noncomputable section
open scoped unitInterval
namespace Cubical

variable {X : Type*} [TopologicalSpace X]

/-- Every actual finite one-cycle in a contractible space has an actual
normalized cubical filling. No regularity of its parameterized edges is needed. -/
theorem isNullHomologous_of_boundaryOne_eq_zero [ContractibleSpace X]
    (Γ : OneChain X) (hΓ : boundaryOne Γ = 0) : IsNullHomologous Γ := by
  obtain ⟨p, ⟨H⟩⟩ := id_nullhomotopic X
  let edge : X → C(I, X) := fun x =>
    H.toContinuousMap.comp ⟨fun t => (t, x), by fun_prop⟩
  let square : C(I, X) → C(I × I, X) := fun γ =>
    H.toContinuousMap.comp ⟨fun t => (t.1, γ t.2), by fun_prop⟩
  have hL (γ : C(I, X)) : left (square γ) = γ := by
    ext t
    simp [left, square]
  have hR (γ : C(I, X)) : right (square γ) = ContinuousMap.const I p := by
    ext t
    simp [right, square]
  have hB (γ : C(I, X)) : bottom (square γ) = edge (γ 0) := by
    ext t
    rfl
  have hT (γ : C(I, X)) : top (square γ) = edge (γ 1) := by
    ext t
    rfl
  let Q : OneChain X →ₗ[ℤ] TwoChain X :=
    Finsupp.linearCombination ℤ (fun γ => Finsupp.single (square γ) 1)
  let D : OneChain X →ₗ[ℤ] (X →₀ ℤ) :=
    Finsupp.linearCombination ℤ (fun _ => Finsupp.single p 1)
  let E : (X →₀ ℤ) →ₗ[ℤ] OneChain X :=
    Finsupp.linearCombination ℤ (fun x => Finsupp.single (edge x) 1)
  have hfill : boundaryTwo.comp Q =
      constantChain.comp D - LinearMap.id - E.comp boundaryOne := by
    apply Finsupp.lhom_ext
    intro γ k
    simp only [LinearMap.comp_apply, Q, D, E, Finsupp.linearCombination_single,
      boundaryTwo, constantChain, boundaryOne, squareBoundary,
      hL, hR, hB, hT, map_sub, LinearMap.sub_apply, LinearMap.id_apply,
      smul_add, smul_sub, Finsupp.smul_single_one]
    abel
  have heq := LinearMap.congr_fun hfill Γ
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hΓ, map_zero, sub_zero] at heq
  refine ⟨-(Q Γ), D Γ, ?_⟩
  rw [map_neg, heq]
  abel

/-- A finite cycle supported in an actual contractible subset has an actual
normalized filling in that subset. The returned lifted chain keeps the
original edges and coefficients, so corners and stationary points are retained. -/
theorem exists_isNullHomologous_mapOne_subtype_val_eq (Γ : OneChain X) (S : Set X)
    [ContractibleSpace S] (hΓ : boundaryOne Γ = 0)
    (hs : ∀ γ ∈ Γ.support, ∀ t, γ t ∈ S) :
    ∃ Δ : OneChain S,
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) Δ = Γ ∧
        IsNullHomologous Δ := by
  obtain ⟨Δ, hΔ⟩ := exists_mapOne_subtype_val_eq Γ S hs
  refine ⟨Δ, hΔ, isNullHomologous_of_boundaryOne_eq_zero Δ ?_⟩
  apply mapZero_injective (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X))
    Subtype.val_injective
  rw [map_zero, ← boundaryOne_mapOne, hΔ, hΓ]

end Cubical
