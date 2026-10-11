/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.ExactSignActions

set_option autoImplicit false

/-!
# Exact sparse selection-law symmetry

Signed-permutation invariance of iid weights, compatible choices, and selection kernels.
Ported from `SparseFockFormal.UniformExactSSymmetry` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators

namespace NLAlib.SparseFock.UniformExactS

open SparseIIDCoupling SparseStackModel

noncomputable section

/-! ## The signed coordinate action -/

/-- Signed coordinate permutations are equivalences of exact columns.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def transformColumnEquiv {m s : ℕ} (pi : Equiv.Perm (Fin m))
    (eps : Fin m → Sign) : ExactColumn m s ≃ ExactColumn m s where
  toFun := transformColumn pi eps
  invFun := transformColumn pi.symm (inverseMask pi eps)
  left_inv := transformColumn_inverse_left pi eps
  right_inv := transformColumn_inverse_right pi eps

/-! ## Preservation of the iid mass and fill/thin geometry -/

/-- The nested iid law weight equals its product over flattened coordinate labels.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem nestedYLaw_weight_eq_flat_prod {b s : ℕ} (hb : 0 < b)
    (y : NestedY b s) :
    (nestedYLaw hb s).weight y =
      ∏ r : Fin (s * b), TernaryJacobi.mass b (flatOutcome y r) := by
  rw [nestedYLaw_weight]
  simp_rw [yVectorLaw_weight]
  calc
    (∏ g : Fin s, ∏ a : Fin b, TernaryJacobi.mass b (y g a)) =
        ∏ ga : Fin s × Fin b, TernaryJacobi.mass b (y ga.1 ga.2) :=
      (Fintype.prod_prod_type
        (fun ga : Fin s × Fin b => TernaryJacobi.mass b (y ga.1 ga.2))).symm
    _ = ∏ ga : Fin s × Fin b,
        TernaryJacobi.mass b (flatOutcome y (finProdFinEquiv ga)) := by
      apply Finset.prod_congr rfl
      intro ga _
      rw [flatOutcome_pair]
    _ = ∏ r : Fin (s * b), TernaryJacobi.mass b (flatOutcome y r) :=
      finProdFinEquiv.prod_comp
        (fun r : Fin (s * b) => TernaryJacobi.mass b (flatOutcome y r))

/-- The nested iid law is invariant under signed coordinate permutations.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem nestedYLaw_weight_transformY {b s : ℕ} (hb : 0 < b)
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) :
    (nestedYLaw hb s).weight (transformY pi eps y) =
      (nestedYLaw hb s).weight y := by
  rw [nestedYLaw_weight_eq_flat_prod hb, nestedYLaw_weight_eq_flat_prod hb]
  simp_rw [flatOutcome_transformY, mass_actOutcome]
  exact pi.symm.prod_comp
    (fun r : Fin (s * b) => TernaryJacobi.mass b (flatOutcome y r))

/-- The flattened support transforms by the recorded coordinate permutation.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem flatSupport_transformY {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) :
    flatSupport (transformY pi eps y) =
      (flatSupport y).map pi.toEmbedding := by
  ext r
  simp [flatSupport, flatOutcome_transformY]

/-- Signed coordinate permutations preserve total support cardinality.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem totalSupport_transformY {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) :
    totalSupport (transformY pi eps y) = totalSupport y := by
  rw [totalSupport, totalSupport, flatSupport_transformY]
  simp

/-- Compatibility is invariant under simultaneous signed permutations.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem compatible_transform_iff {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) (x : ExactColumn (s * b) s) :
    Compatible (transformY pi eps y) (transformColumn pi eps x) ↔
      Compatible y x := by
  classical
  rw [Compatible, Compatible, totalSupport_transformY]
  split_ifs with hlarge
  · constructor
    · rintro ⟨hsub, hsign⟩
      constructor
      · intro r hr
        have hmap : pi r ∈
            ((transformColumn pi eps x).1 : Finset (Fin (s * b))) := by
          simpa [transformColumn] using hr
        have hy := hsub hmap
        simpa [flatSupport_transformY] using hy
      · intro r hr
        have hmap : pi r ∈
            ((transformColumn pi eps x).1 : Finset (Fin (s * b))) := by
          simpa [transformColumn] using hr
        have hs := hsign (pi r) hmap
        have hs' := congrArg (actOutcome (eps (pi r))) hs
        simpa [flatOutcome_transformY, transformColumn] using hs'
    · rintro ⟨hsub, hsign⟩
      constructor
      · intro r hr
        have hr' : pi.symm r ∈ (x.1 : Finset (Fin (s * b))) := by
          simpa [transformColumn] using hr
        have hy := hsub hr'
        simpa [flatSupport_transformY] using hy
      · intro r hr
        have hr' : pi.symm r ∈ (x.1 : Finset (Fin (s * b))) := by
          simpa [transformColumn] using hr
        have hs := hsign (pi.symm r) hr'
        simpa [flatOutcome_transformY, transformColumn] using
          congrArg (actOutcome (eps r)) hs
  · constructor
    · rintro ⟨hsub, hsign⟩
      constructor
      · intro r hr
        have hmap : pi r ∈ flatSupport (transformY pi eps y) := by
          simpa [flatSupport_transformY] using hr
        have hx := hsub hmap
        simpa [transformColumn] using hx
      · intro r hr
        have hmap : pi r ∈ flatSupport (transformY pi eps y) := by
          simpa [flatSupport_transformY] using hr
        have hs := hsign (pi r) hmap
        have hs' := congrArg (actOutcome (eps (pi r))) hs
        simpa [flatOutcome_transformY, transformColumn] using hs'
    · rintro ⟨hsub, hsign⟩
      constructor
      · intro r hr
        have hr' : pi.symm r ∈ flatSupport y := by
          simpa [flatSupport_transformY] using hr
        have hx := hsub hr'
        simpa [transformColumn] using hx
      · intro r hr
        have hr' : pi.symm r ∈ flatSupport y := by
          simpa [flatSupport_transformY] using hr
        have hs := hsign (pi.symm r) hr'
        simpa [flatOutcome_transformY, transformColumn] using
          congrArg (actOutcome (eps r)) hs

/-! ## Kernel weights and induced fiber equivalences -/

/-- Since `Subtype.val` is injective, a pushed uniform compatible-choice law
has exactly one preimage at a compatible column.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem selectionKernel_weight_of_compatible {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (y : NestedY b s) (x : ExactColumn (s * b) s)
    (hxy : Compatible y x) :
    (selectionKernel hb hs y).weight x =
      1 / (Nat.card (ChoiceColumn y) : ℝ) := by
  classical
  let : Nonempty (ChoiceColumn y) := choiceColumn_nonempty hb hs y
  let c : ChoiceColumn y := ⟨x, hxy⟩
  rw [selectionKernel, FiniteLaw.map_weight,
    Finset.sum_eq_single c]
  · rw [if_pos (by rfl)]
    change 1 / (Fintype.card (ChoiceColumn y) : ℝ) =
        1 / (Nat.card (ChoiceColumn y) : ℝ)
    rw [Fintype.card_eq_nat_card]
  · intro z _ hz
    have hne : (z : ExactColumn (s * b) s) ≠ x := by
      intro h
      apply hz
      apply Subtype.ext
      exact h
    simp [hne]
  · simp

/-- An incompatible column has no preimage under the compatible-choice map.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem selectionKernel_weight_of_not_compatible {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (y : NestedY b s) (x : ExactColumn (s * b) s)
    (hxy : ¬ Compatible y x) :
    (selectionKernel hb hs y).weight x = 0 := by
  classical
  let : Nonempty (ChoiceColumn y) := choiceColumn_nonempty hb hs y
  rw [selectionKernel, FiniteLaw.map_weight]
  apply Finset.sum_eq_zero
  intro z _
  have hne : (z : ExactColumn (s * b) s) ≠ x := by
    intro h
    apply hxy
    simpa [h] using z.prop
  simp [hne]

/-- Simultaneous signed permutation gives an equivalence of compatible-choice
fibers.

Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def transformChoiceEquiv {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) :
    ChoiceColumn y ≃ ChoiceColumn (transformY pi eps y) where
  toFun c := ⟨transformColumn pi eps c.1,
    (compatible_transform_iff pi eps y c.1).2 c.2⟩
  invFun c := ⟨transformColumn pi.symm (inverseMask pi eps) c.1, by
    have hc := (compatible_transform_iff pi.symm (inverseMask pi eps)
      (transformY pi eps y) c.1).2 c.2
    simpa using hc⟩
  left_inv c := by
    apply Subtype.ext
    exact transformColumn_inverse_left pi eps c.1
  right_inv c := by
    apply Subtype.ext
    exact transformColumn_inverse_right pi eps c.1

/-- Signed coordinate permutations preserve the number of compatible exactly-s selector columns.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem choiceColumn_card_transform {b s : ℕ}
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) :
    Nat.card (ChoiceColumn (transformY pi eps y)) =
      Nat.card (ChoiceColumn y) := by
  exact (Nat.card_congr (transformChoiceEquiv pi eps y)).symm

/-- Jointly transforming iid outcomes and exact columns preserves selection-kernel mass.
Source: ported from `SparseFockFormal.UniformExactSSymmetry`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem selectionKernel_weight_transform {b s : ℕ}
    (hb : 0 < b) (hs : 0 < s)
    (pi : Equiv.Perm (Fin (s * b))) (eps : Fin (s * b) → Sign)
    (y : NestedY b s) (x : ExactColumn (s * b) s) :
    (selectionKernel hb hs (transformY pi eps y)).weight
        (transformColumn pi eps x) =
      (selectionKernel hb hs y).weight x := by
  by_cases hxy : Compatible y x
  · have ht : Compatible (transformY pi eps y)
        (transformColumn pi eps x) :=
      (compatible_transform_iff pi eps y x).2 hxy
    rw [selectionKernel_weight_of_compatible hb hs _ _ ht,
      selectionKernel_weight_of_compatible hb hs _ _ hxy,
      choiceColumn_card_transform]
  · have ht : ¬ Compatible (transformY pi eps y)
        (transformColumn pi eps x) := by
      simpa [compatible_transform_iff pi eps y x] using hxy
    rw [selectionKernel_weight_of_not_compatible hb hs _ _ ht,
      selectionKernel_weight_of_not_compatible hb hs _ _ hxy]

end

end NLAlib.SparseFock.UniformExactS
