import NLAlib.Polynomial.BestApproximation.NodeSimplex
import NLAlib.Polynomial.BestApproximation.InterpolationProjection
import NLAlib.ForMathlib.LinearAlgebra.LagrangeAffine

/-!
# Affine invariance and canonical node-hull reduction

Stretching the extreme nodes to the unit-interval endpoints preserves cardinal
values and cannot increase the original whole-interval Lebesgue constant.
Helpers for `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Set Finset

namespace NLAlib

/-- Applying the same nondegenerate affine map to nodes and point preserves the Lebesgue function.
Source: cancellation in each finite cardinal product; universal-bound helper. -/
theorem lebesgueFunction_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (x α β : ℝ) (hα : α ≠ 0) :
    lebesgueFunction (fun j => α * v j + β) (α * x + β) = lebesgueFunction v x := by
  unfold lebesgueFunction
  apply sum_congr rfl
  intro j _
  rw [eval_lagrange_basis_affine univ v j x α β hα]

/-- Restricting the approximation interval can only decrease the Lebesgue constant.
Source: the supremum norm on a subset; universal-bound helper. -/
theorem lebesgueConstant_subset_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s t : Set ℝ} [CompactSpace s] [CompactSpace t] (v : ι → ℝ) (hst : s ⊆ t) :
    lebesgueConstant s v ≤ lebesgueConstant t v :=
  lebesgueConstant_le_of_forall v (norm_nonneg _)
    (fun _ hx => lebesgueFunction_le_lebesgueConstant v (hst hx))

/-- Positive affine transplantation preserves the interval Lebesgue constant.
Source: the exact affine cardinal identity; universal-bound helper. -/
theorem lebesgueConstant_affine_interval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (a b α β : ℝ) (hα : 0 < α) :
    lebesgueConstant (Icc (α * a + β) (α * b + β)) (fun j => α * v j + β) =
      lebesgueConstant (Icc a b) v := by
  apply le_antisymm
  · apply lebesgueConstant_le_of_forall _ (norm_nonneg _)
    intro y hy
    have hx : (y - β) / α ∈ Icc a b := by
      constructor
      · apply (le_div_iff₀ hα).mpr
        linarith [hy.1]
      · apply (div_le_iff₀ hα).mpr
        linarith [hy.2]
    have heq : α * ((y - β) / α) + β = y := by field_simp; ring
    rw [← heq, lebesgueFunction_affine _ _ _ _ hα.ne']
    exact lebesgueFunction_le_lebesgueConstant _ hx
  · apply lebesgueConstant_le_of_forall _ (norm_nonneg _)
    intro x hx
    have hy : α * x + β ∈ Icc (α * a + β) (α * b + β) := by
      constructor
      · linarith [mul_le_mul_of_nonneg_left hx.1 hα.le]
      · linarith [mul_le_mul_of_nonneg_left hx.2 hα.le]
    rw [← lebesgueFunction_affine v x α β hα.ne']
    exact lebesgueFunction_le_lebesgueConstant _ hy

/-- An ordered grid with at least two nodes is a positive affine image of a
canonical grid. Source: focused reroutes, stretching the node hull. -/
theorem exists_canonical_nodes_affine {n : ℕ} (v : Fin (n + 2) → ℝ)
    (hv : StrictMono v) :
    ∃ t ∈ interiorNodeSimplex n, ∃ α > 0, ∃ β : ℝ,
      ∀ j, α * canonicalIntervalNodes n t j + β = v j := by
  let a : ℝ := v 0
  let b : ℝ := v (Fin.last (n + 1))
  have hab : a < b := hv (by simp [Fin.lt_def])
  let α : ℝ := (b - a) / 2
  let β : ℝ := (a + b) / 2
  have hα : 0 < α := by dsimp [α]; linarith
  let u : Fin (n + 2) → ℝ := fun j => (v j - β) / α
  have hrep (j : Fin (n + 2)) : α * u j + β = v j := by
    dsimp [u]
    field_simp
    ring
  have hu0 : u 0 = -1 := by
    apply (div_eq_iff hα.ne').mpr
    change v 0 - β = -1 * α
    dsimp [α, β, a, b]
    ring
  have hulast : u (Fin.last (n + 1)) = 1 := by
    apply (div_eq_iff hα.ne').mpr
    change v (Fin.last (n + 1)) - β = 1 * α
    dsimp [α, β, a, b]
    ring
  have humono : StrictMono u := fun i j hij =>
    div_lt_div_of_pos_right (sub_lt_sub_right (hv hij) β) hα
  let t : Fin n → ℝ := fun j => u j.castSucc.succ
  have hcan : canonicalIntervalNodes n t = u := by
    funext j
    refine Fin.cases (by simp [hu0]) (fun i => ?_) j
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [show (Fin.last n).succ = Fin.last (n + 1) by rfl]
      rw [canonicalIntervalNodes_last, hulast]
    · exact canonicalIntervalNodes_interior n t k
  refine ⟨t, ?_, α, hα, β, ?_⟩
  · change StrictMono (canonicalIntervalNodes n t)
    rw [hcan]
    exact humono
  · intro j
    rw [hcan]
    exact hrep j

/-- Every ordered grid with at least two nodes has a canonical stretched grid
whose unit-interval Lebesgue constant is no larger than the original one.
Source: focused reroutes, reduction to canonical node hulls; universal-bound helper. -/
theorem exists_canonical_nodes_le_lebesgueConstant {n : ℕ} (v : Fin (n + 2) → ℝ)
    (hv : StrictMono v) (hvI : ∀ j, v j ∈ Icc (-1 : ℝ) 1) :
    ∃ t ∈ interiorNodeSimplex n,
      lebesgueConstant (Icc (-1 : ℝ) 1) (canonicalIntervalNodes n t) ≤
        lebesgueConstant (Icc (-1 : ℝ) 1) v := by
  obtain ⟨t, ht, α, hα, β, hrep⟩ := exists_canonical_nodes_affine v hv
  have hleft : α * -1 + β = v 0 := by simpa using hrep 0
  have hright : α * 1 + β = v (Fin.last (n + 1)) := by
    simpa using hrep (Fin.last (n + 1))
  have hnodes : (fun j => α * canonicalIntervalNodes n t j + β) = v := funext hrep
  have hnorm := lebesgueConstant_affine_interval (canonicalIntervalNodes n t) (-1) 1 α β hα
  rw [hleft, hright, hnodes] at hnorm
  refine ⟨t, ht, ?_⟩
  rw [← hnorm]
  exact lebesgueConstant_subset_le v (Icc_subset_Icc (hvI 0).1 (hvI (Fin.last _)).2)

end NLAlib
