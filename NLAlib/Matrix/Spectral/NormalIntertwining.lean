import NLAlib.Matrix.Spectral.NormalSpectral
import Mathlib.Analysis.CStarAlgebra.Fuglede
/-!
# Fuglede–Putnam for normal matrices

The abstract C⋆-algebra theorem specializes to complex square matrices.
Source: Horn–Johnson (2013), Theorem 2.5.15;
atlas `normal-matrices`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Intertwining complex normal matrices is unchanged by taking adjoints.
Source: Horn–Johnson (2013), Theorem 2.5.15; Mathlib's
Fuglede–Putnam–Rosenblum theorem supplies the C⋆-algebra proof.
atlas: normal-matrices (partial) -/
theorem mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose_of_normal
    {A B X : Matrix n n ℂ} (hA : A * Aᴴ = Aᴴ * A)
    (hB : B * Bᴴ = Bᴴ * B) : A * X = X * B ↔ Aᴴ * X = X * Bᴴ := by
  cases isEmpty_or_nonempty n with
  | inl hn => exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | inr hn =>
    let : IsStarNormal A := ⟨hA.symm⟩
    let : IsStarNormal B := ⟨hB.symm⟩
    constructor
    · intro h
      exact (SemiconjBy.star_right ⟨hB.symm⟩ ⟨hA.symm⟩
        (show SemiconjBy X B A from h.symm)).symm
    · intro h
      have h' := SemiconjBy.star_right (inferInstance : IsStarNormal (star B))
        (inferInstance : IsStarNormal (star A))
        (show SemiconjBy X (star B) (star A) from h.symm)
      simpa only [star_star] using h'.symm

end NLAlib
