import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FinCases

/-!
# Singleton and pair principal minors

The small inclusion moments of a determinantal law use these coordinate
identities. They hold over any commutative ring and any ambient index type.
-/

noncomputable section

namespace Matrix

variable {R n : Type*} [CommRing R] [DecidableEq n]

/-- A singleton principal determinant is the matching diagonal entry. -/
theorem det_submatrix_singleton (M : Matrix n n R) (i : n) :
    (M.submatrix (Subtype.val : ↥({i} : Finset n) → n)
      (Subtype.val : ↥({i} : Finset n) → n)).det = M i i := by
  classical
  let _ : Unique ↥({i} : Finset n) :=
    { default := ⟨i, by simp⟩
      uniq := fun j => Subtype.ext (Finset.mem_singleton.mp j.property) }
  have hd : ((default : ↥({i} : Finset n)) : n) = i :=
    Finset.mem_singleton.mp (default : ↥({i} : Finset n)).property
  simpa only [Matrix.submatrix_apply, hd] using
    det_unique (M.submatrix (Subtype.val : ↥({i} : Finset n) → n)
      (Subtype.val : ↥({i} : Finset n) → n))

/-- A pair principal determinant is the ordinary two-by-two determinant,
with distinct ambient indices in either order. -/
theorem det_submatrix_pair (M : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (M.submatrix (Subtype.val : ↥({i, j} : Finset n) → n)
      (Subtype.val : ↥({i, j} : Finset n) → n)).det =
      M i i * M j j - M i j * M j i := by
  classical
  let f : Fin 2 → ↥({i, j} : Finset n) := fun a =>
    if a = 0 then ⟨i, by simp⟩ else ⟨j, by simp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have he := congrArg Subtype.val h
      fin_cases a <;> fin_cases b <;> simp_all [f]
    · intro a
      have ha := a.property
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [f] using ha.symm
      · refine ⟨1, ?_⟩
        apply Subtype.ext
        simpa [f] using ha.symm
  let e := Equiv.ofBijective f hf
  rw [← det_submatrix_equiv_self e
    (M.submatrix (Subtype.val : ↥({i, j} : Finset n) → n)
      (Subtype.val : ↥({i, j} : Finset n) → n)), det_fin_two]
  simp [e, f, Matrix.submatrix_apply]

end Matrix
