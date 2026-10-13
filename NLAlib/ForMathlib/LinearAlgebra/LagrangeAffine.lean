import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp

/-!
# Affine invariance of Lagrange cardinal functions

An affine change of the evaluation point and all nodes preserves each cardinal
value. Helper for `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Polynomial Finset

namespace NLAlib

/-- A nondegenerate affine change preserves Lagrange cardinal values.
Source: cancellation in the cardinal product; helper for `lebesgue-constant-lower-bound`. -/
theorem eval_lagrange_basis_affine {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (i : ι) (x α β : F) (hα : α ≠ 0) :
    (Lagrange.basis s (fun j => α * v j + β) i).eval (α * x + β) =
      (Lagrange.basis s v i).eval x := by
  simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor,
    eval_mul, eval_C, eval_sub, eval_X]
  apply prod_congr rfl
  intro j _
  rw [show α * v i + β - (α * v j + β) = α * (v i - v j) by ring,
    show α * x + β - (α * v j + β) = α * (x - v j) by ring, mul_inv_rev]
  calc
    _ = ((v i - v j)⁻¹ * (x - v j)) * (α⁻¹ * α) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hα, mul_one]

/-- Indexing the same finite grid by `Fin n` or by `range n` gives the same cardinal.
Source: reindexing the finite cardinal product; helper for `lebesgue-constant-lower-bound`. -/
theorem lagrange_basis_univ_fin_eq_range {F : Type*} [Field F] (n : ℕ)
    (v : ℕ → F) (j : Fin n) :
    Lagrange.basis univ (fun k : Fin n => v k) j = Lagrange.basis (range n) v j := by
  simp only [Lagrange.basis]
  apply prod_bij (fun k _ => k.val)
  · intro k hk
    have hkj : k ≠ j := (mem_erase.mp hk).1
    exact mem_erase.mpr ⟨(fun h => hkj (Fin.ext h)), mem_range.mpr k.isLt⟩
  · intro k _ l _ hkl
    exact Fin.ext hkl
  · intro k hk
    obtain ⟨hkj, hk⟩ := mem_erase.mp hk
    refine ⟨⟨k, mem_range.mp hk⟩, mem_erase.mpr ⟨?_, mem_univ _⟩, rfl⟩
    intro h
    exact hkj (congrArg Fin.val h)
  · intro k _
    rfl

end NLAlib
