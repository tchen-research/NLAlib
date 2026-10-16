import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Restriction and irreducible subrepresentations

Subrepresentations of a restricted representation correspond to invariant
subspaces below the original subrepresentation. Finite dimension then gives
an irreducible subrepresentation inside every nonzero invariant subspace.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation
namespace Subrepresentation

variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- Inclusion of an invariant subspace is an actual intertwining map. -/
def subtype (S : Subrepresentation ρ) : IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/-- Push an invariant subspace forward along an intertwining map. -/
def map (S : Subrepresentation ρ) (f : IntertwiningMap ρ σ) : Subrepresentation σ where
  toSubmodule := S.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv,
      Representation.IntertwiningMap.isIntertwining ρ σ f g v⟩

/-- Pull an invariant subspace back along an intertwining map. -/
def comap (S : Subrepresentation σ) (f : IntertwiningMap ρ σ) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change f (ρ g v) ∈ S
    rw [Representation.IntertwiningMap.isIntertwining ρ σ f]
    exact S.apply_mem_toSubmodule g hv

/-- Invariant subspaces of a restricted representation are precisely the
invariant subspaces contained in its original domain. -/
def subtypeOrderIso (S : Subrepresentation ρ) :
    Subrepresentation S.toRepresentation ≃o Set.Iic S where
  toFun T := ⟨T.map S.subtype, by
    rintro _ ⟨v, hv, rfl⟩
    exact v.property⟩
  invFun T := T.val.comap S.subtype
  left_inv T := by
    apply toSubmodule_injective
    exact Submodule.comap_map_eq_of_injective S.toSubmodule.subtype_injective T.toSubmodule
  right_inv T := by
    apply Subtype.ext
    apply toSubmodule_injective
    change Submodule.map S.toSubmodule.subtype
      (Submodule.comap S.toSubmodule.subtype T.val.toSubmodule) = T.val.toSubmodule
    rw [Submodule.map_comap_subtype, inf_of_le_right T.property]
  map_rel_iff' := by
    intro A B
    exact Submodule.map_le_map_iff_of_injective S.toSubmodule.subtype_injective
      A.toSubmodule B.toSubmodule

/-- A restricted representation is irreducible exactly when its subspace is
an atom of the invariant-subspace lattice. -/
theorem isIrreducible_toRepresentation_iff (S : Subrepresentation ρ) :
    IsIrreducible S.toRepresentation ↔ IsAtom S := by
  change IsSimpleOrder (Subrepresentation S.toRepresentation) ↔ IsAtom S
  rw [← Set.isSimpleOrder_Iic_iff_isAtom]
  exact (S.subtypeOrderIso).isSimpleOrder_iff

/-- Every nonzero invariant subspace of a finite-dimensional representation
contains an actual irreducible subrepresentation. -/
theorem exists_irreducible_le [FiniteDimensional k V]
    (S : Subrepresentation ρ) (hS : S ≠ ⊥) :
    ∃ T : Subrepresentation ρ, T ≤ S ∧ IsIrreducible T.toRepresentation := by
  have hwf : WellFounded ((· < ·) : Subrepresentation ρ → Subrepresentation ρ → Prop) := by
    apply (measure (fun T : Subrepresentation ρ => Module.finrank k T.toSubmodule)).wf.mono
    intro A B hAB
    exact Submodule.finrank_lt_finrank_of_lt hAB
  letI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt hwf
  obtain hbot | ⟨T, hT, hTS⟩ := eq_bot_or_exists_atom_le S
  · exact (hS hbot).elim
  · exact ⟨T, hTS, (isIrreducible_toRepresentation_iff T).mpr hT⟩

end Subrepresentation
