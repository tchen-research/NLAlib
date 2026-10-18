import NLAlib.ForMathlib.Topology.CubicalChainHomotopy
import Mathlib.Topology.Subpath
import Mathlib.Algebra.BigOperators.Fin

/-! # Native finite path concatenations as actual cubical chains

The actual finite path pieces determine a one-chain whose endpoint boundary
telescopes. Their native concatenation differs by a constructed normalized
two-chain boundary. No differentiability at the joins is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Finset
open scoped unitInterval

namespace Path

/-- A continuous map preserves an actual finite native path concatenation. -/
theorem map_concat {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} (p : Fin (n + 1) → X)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    {f : X → Y} (hf : Continuous f) :
    (concat p γ).map hf = concat (fun i => f (p i)) (fun i => (γ i).map hf) := by
  induction n with
  | zero => simp only [concat_zero]; ext t; rfl
  | succ n ih =>
    rw [concat_succ]
    erw [map_trans, concat_succ, ih]
    rfl

end Path

namespace Cubical

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- The actual finite chain of a composable native path family. -/
def pathChain (p : Fin (n + 1) → X)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ)) : OneChain X :=
  ∑ i, Finsupp.single (γ i).toContinuousMap 1

/-- Every active edge of the finite path chain is an actual supplied piece. -/
theorem exists_piece_of_mem_support_pathChain (p : Fin (n + 1) → X)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    {q : C(I, X)} (hq : q ∈ (pathChain p γ).support) :
    ∃ i, (γ i).toContinuousMap = q := by
  classical
  by_contra hnot
  have hz : pathChain p γ q = 0 := by
    simp only [pathChain, Finsupp.finsetSum_apply]
    apply sum_eq_zero
    intro i _
    have hne : (γ i).toContinuousMap ≠ q := fun h => hnot ⟨i, h⟩
    simp [hne]
  exact (Finsupp.mem_support_iff.mp hq) hz

/-- Only the first and last endpoints survive the actual chain boundary. -/
theorem boundaryOne_pathChain (p : Fin (n + 1) → X)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ)) :
    boundaryOne (pathChain p γ) = Finsupp.single (p (Fin.last n)) 1 -
      Finsupp.single (p 0) 1 := by
  simp only [pathChain, map_sum, boundaryOne, Finsupp.linearCombination_single,
    one_smul, Path.coe_toContinuousMap, Path.source, Path.target]
  rw [sum_sub_distrib]
  let f : Fin (n + 1) → X →₀ ℤ := fun i => Finsupp.single (p i) 1
  change (∑ i : Fin n, f i.succ) - (∑ i : Fin n, f i.castSucc) = f (Fin.last n) - f 0
  have hs : (∑ i : Fin n, f i.succ) = (∑ i, f i) - f 0 := by
    rw [Fin.sum_univ_succ]
    abel
  have ht : (∑ i : Fin n, f i.castSucc) = (∑ i, f i) - f (Fin.last n) := by
    rw [Fin.sum_univ_castSucc]
    abel
  rw [hs, ht]
  abel

/-- Endpoint closure makes the actual finite path chain a cycle. -/
theorem boundaryOne_pathChain_eq_zero (p : Fin (n + 1) → X)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ)) (hp : p (Fin.last n) = p 0) :
    boundaryOne (pathChain p γ) = 0 := by
  rw [boundaryOne_pathChain, hp, sub_self]

/-- Finite native concatenation and the sum of its actual path pieces
represent the same normalized cubical homology class, including empty chains. -/
theorem isNullHomologous_single_concat_sub_pathChain (p : Fin (n + 1) → X)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ)) :
    IsNullHomologous (Finsupp.single (Path.concat p γ).toContinuousMap 1 - pathChain p γ) := by
  induction n with
  | zero =>
    refine ⟨0, Finsupp.single (p 0) 1, ?_⟩
    simp [pathChain, constantChain]
    rfl
  | succ n ih =>
    have hs := isNullHomologous_single_trans_sub
      (Path.concat (p ∘ Fin.castSucc) (fun i => γ i.castSucc)) (γ (Fin.last n))
    have ht := hs.add (ih (p ∘ Fin.castSucc) (fun i => γ i.castSucc))
    convert ht using 1
    simp only [Path.concat_succ, pathChain, Fin.sum_univ_castSucc]
    abel

end Cubical
