import Mathlib.LinearAlgebra.Lagrange

/-! # Reindexing finite Lagrange cardinal polynomials

Bijections of a finite node index leave the cardinal polynomials unchanged.
-/
noncomputable section
open Polynomial Finset
namespace NLAlib

/-- Reindexing a finite grid reindexes its cardinal polynomial.
Source: the finite Lagrange product; interpolation reference-grid helper. -/
theorem lagrange_basis_univ_comp_equiv {F ι κ : Type*} [Field F]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (v : ι → F) (e : κ ≃ ι) (i : κ) :
    Lagrange.basis univ (v ∘ e) i = Lagrange.basis univ v (e i) := by
  unfold Lagrange.basis
  apply prod_bij (fun j _ => e j)
  · intro j hj
    exact mem_erase.mpr ⟨(fun h => (mem_erase.mp hj).1 (e.injective h)), mem_univ _⟩
  · intro j _ k _ h
    exact e.injective h
  · intro j hj
    refine ⟨e.symm j, mem_erase.mpr ⟨?_, mem_univ _⟩, e.apply_symm_apply j⟩
    intro h
    exact (mem_erase.mp hj).1 (by simpa only [e.apply_symm_apply] using congrArg e h)
  · intro j hj
    rfl

end NLAlib
