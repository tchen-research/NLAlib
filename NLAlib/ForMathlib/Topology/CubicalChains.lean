import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel

/-! # Finite singular cubical chains in dimensions one and two

A one-chain is a finite integer combination of actual continuous interval
maps. A two-chain is a finite integer combination of actual continuous square
maps. Their alternating face boundaries give a precise topological
null-homology witness independently of any integration theorem.
-/

noncomputable section
open scoped unitInterval
namespace Cubical

variable (X : Type*) [TopologicalSpace X]

/-- Finite singular cubical one-chains with integer coefficients. -/
abbrev OneChain := C(I, X) →₀ ℤ

/-- Finite singular cubical two-chains with integer coefficients. -/
abbrev TwoChain := C(I × I, X) →₀ ℤ

variable {X}

/-- The left continuous face of a singular square. -/
def left (q : C(I × I, X)) : C(I, X) :=
  q.comp ⟨fun t => (0, t), by fun_prop⟩

/-- The right continuous face of a singular square. -/
def right (q : C(I × I, X)) : C(I, X) :=
  q.comp ⟨fun t => (1, t), by fun_prop⟩

/-- The bottom continuous face of a singular square. -/
def bottom (q : C(I × I, X)) : C(I, X) :=
  q.comp ⟨fun t => (t, 0), by fun_prop⟩

/-- The top continuous face of a singular square. -/
def top (q : C(I × I, X)) : C(I, X) :=
  q.comp ⟨fun t => (t, 1), by fun_prop⟩

/-- The alternating boundary of a singular square. Every face uses its
increasing coordinate, with the signs giving counterclockwise orientation. -/
def squareBoundary (q : C(I × I, X)) : OneChain X :=
  Finsupp.single (right q) 1 - Finsupp.single (left q) 1 -
    Finsupp.single (top q) 1 + Finsupp.single (bottom q) 1

/-- The boundary map of finite singular cubical two-chains. -/
def boundaryTwo : TwoChain X →ₗ[ℤ] OneChain X :=
  Finsupp.linearCombination ℤ squareBoundary

/-- The endpoint boundary map of finite singular cubical one-chains. -/
def boundaryOne : OneChain X →ₗ[ℤ] (X →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun γ => Finsupp.single (γ 1) 1 - Finsupp.single (γ 0) 1)

/-- Finite integer combinations of degenerate, constant one-cubes. These are
zero in the normalized singular cubical chain complex. -/
def constantChain : (X →₀ ℤ) →ₗ[ℤ] OneChain X :=
  Finsupp.linearCombination ℤ (fun x => Finsupp.single (ContinuousMap.const I x) 1)

/-- A singular cubical cycle is null-homologous when it is the actual
boundary of a finite continuous singular two-chain, modulo degenerate
constant one-cubes as in normalized cubical homology. This condition contains
no analytic or integral hypotheses. -/
def IsNullHomologous (Γ : OneChain X) : Prop :=
  ∃ S : TwoChain X, ∃ D : X →₀ ℤ, boundaryTwo S + constantChain D = Γ

@[simp]
theorem boundaryOne_squareBoundary (q : C(I × I, X)) :
    boundaryOne (squareBoundary q) = 0 := by
  simp only [squareBoundary, map_add, map_sub, boundaryOne,
    Finsupp.linearCombination_single, one_smul, right, left, top, bottom,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  abel

/-- Every actual singular cubical boundary has zero endpoint boundary. -/
theorem boundaryOne_boundaryTwo (S : TwoChain X) : boundaryOne (boundaryTwo S) = 0 := by
  rw [boundaryTwo, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul, boundaryOne_squareBoundary, smul_zero, Finset.sum_const_zero]

@[simp]
theorem boundaryOne_constantChain (D : X →₀ ℤ) : boundaryOne (constantChain D) = 0 := by
  rw [constantChain, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul, boundaryOne, Finsupp.linearCombination_single,
    ContinuousMap.const_apply, sub_self, smul_zero, Finset.sum_const_zero]

/-- In particular, null-homologous one-chains are cycles. -/
theorem IsNullHomologous.boundaryOne_eq_zero {Γ : OneChain X} (hΓ : IsNullHomologous Γ) :
    boundaryOne Γ = 0 := by
  obtain ⟨S, D, rfl⟩ := hΓ
  rw [map_add, boundaryOne_boundaryTwo, boundaryOne_constantChain, add_zero]

end Cubical
