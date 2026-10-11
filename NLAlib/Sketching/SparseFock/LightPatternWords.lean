/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightSynthesisBounds

/-!
# Canonical pattern words and permutation orbits

Partition of the literal shared-leg proof from sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`.
The original `LightSectorConcrete` import re-exports this unchanged namespace.
Supports the `sparse-ose` moment proof.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace NLAlib.SparseFock.LightSectorConcrete
open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert
variable {d m n ell : ℕ}

/-! ### Concrete hard-core block coordinates -/

/-- The patterns in one block have the prescribed heavy set and light count.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev BlockPattern (T : Finset (Site m n)) (ell : ℕ) :=
  {p : Pattern m n // InBlock T ell p}

/-- A block coordinate consists of an external leg and a pattern in that block.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev BlockIndex (d : ℕ) (T : Finset (Site m n)) (ell : ℕ) :=
  Fin d × BlockPattern T ell

/-- A fixed enumeration of the exact light support of a block pattern.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def lightSupportEquiv (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) : Fin ell ≃ p.1.light :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact p.2.2)).symm

/-- A canonical light word enumerates the exact light support of a block pattern.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def canonicalLightWord (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (k : Fin ell) : Site m n :=
  (lightSupportEquiv T ell p k).1

/-- Every site in a canonical light word belongs to the pattern's light support.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem canonicalLightWord_mem (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (k : Fin ell) :
    canonicalLightWord T ell p k ∈ p.1.light :=
  (lightSupportEquiv T ell p k).2

/-- The canonical enumeration of light sites is injective.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem canonicalLightWord_injective (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) :
    Function.Injective (canonicalLightWord T ell p) := by
  intro k l h
  exact (lightSupportEquiv T ell p).injective (Subtype.ext h)

/-- A site is light exactly when it occurs in the canonical light word.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem canonicalLightWord_surjective (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (s : Site m n) :
    s ∈ p.1.light ↔ ∃ k, canonicalLightWord T ell p k = s := by
  constructor
  · intro hs
    obtain ⟨k, hk⟩ := (lightSupportEquiv T ell p).surjective ⟨s, hs⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rintro ⟨k, rfl⟩
    exact canonicalLightWord_mem T ell p k

/-- Every ordering of the light support gives one hard-core tensor word.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def permutedLightWord (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (pi : Equiv.Perm (Fin ell)) :
    Fin ell → Site m n :=
  fun k ↦ canonicalLightWord T ell p (pi k)

/-- The identity permutation leaves each canonical light-word entry unchanged.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem permutedLightWord_refl (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (k : Fin ell) :
    permutedLightWord T ell p (Equiv.refl (Fin ell)) k =
      canonicalLightWord T ell p k := rfl

/-- The identity-permuted light word is the canonical light word.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem permutedLightWord_refl_fun
    (T : Finset (Site m n)) (ell : ℕ) (p : BlockPattern T ell) :
    permutedLightWord T ell p (Equiv.refl (Fin ell)) =
      canonicalLightWord T ell p := rfl

/-- Permuting the canonical light enumeration preserves injectivity.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem permutedLightWord_injective (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (pi : Equiv.Perm (Fin ell)) :
    Function.Injective (permutedLightWord T ell p pi) :=
  (canonicalLightWord_injective T ell p).comp pi.injective

/-- Every site of a permuted light word remains in the light support.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem permutedLightWord_mem (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (pi : Equiv.Perm (Fin ell)) (k : Fin ell) :
    permutedLightWord T ell p pi k ∈ p.1.light :=
  canonicalLightWord_mem T ell p (pi k)

/-- Every light site occurs in every permuted light enumeration.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem permutedLightWord_surjective (T : Finset (Site m n)) (ell : ℕ)
    (p : BlockPattern T ell) (pi : Equiv.Perm (Fin ell)) (s : Site m n) :
    s ∈ p.1.light ↔ ∃ k, permutedLightWord T ell p pi k = s := by
  rw [canonicalLightWord_surjective T ell p s]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨pi.symm k, ?_⟩
    simp [permutedLightWord, hk]
  · rintro ⟨k, hk⟩
    exact ⟨pi k, hk⟩

/-- The unique slot permutation represented by any injective enumeration of
the exact light support.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def permutationOfLightWord
    (T : Finset (Site m n)) (ell : ℕ) (p : BlockPattern T ell)
    (w : Fin ell → Site m n)
    (hmem : ∀ k, w k ∈ p.1.light) (hinj : Function.Injective w) :
    Equiv.Perm (Fin ell) := by
  let f : Fin ell → p.1.light := fun k ↦ ⟨w k, hmem k⟩
  have hfInj : Function.Injective f := by
    intro k l h
    exact hinj (congrArg Subtype.val h)
  have hcard : Fintype.card (Fin ell) = Fintype.card p.1.light := by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact p.2.2.symm
  let e : Fin ell ≃ p.1.light :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfInj, hcard⟩)
  exact e.trans (lightSupportEquiv T ell p).symm

/-- The permutation recovered from an injective light enumeration reconstructs that enumeration.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem permutedLightWord_permutationOfLightWord
    (T : Finset (Site m n)) (ell : ℕ) (p : BlockPattern T ell)
    (w : Fin ell → Site m n)
    (hmem : ∀ k, w k ∈ p.1.light) (hinj : Function.Injective w) :
    permutedLightWord T ell p
      (permutationOfLightWord T ell p w hmem hinj) = w := by
  funext k
  simp [permutedLightWord, permutationOfLightWord, canonicalLightWord]

/-- A pattern is determined by its light and heavy supports.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pattern_eq_of_light_heavy_eq {p q : Pattern m n}
    (hlight : p.light = q.light) (hheavy : p.heavy = q.heavy) : p = q := by
  funext s
  have hL : (p s = .one) ↔ (q s = .one) := by
    rw [← Pattern.mem_light, ← Pattern.mem_light, hlight]
  have hH : (p s = .two) ↔ (q s = .two) := by
    rw [← Pattern.mem_heavy, ← Pattern.mem_heavy, hheavy]
  cases hp : p s <;> cases hq : q s <;> simp_all

/-- Equality of two enumerated hard-core words recovers the underlying block
pattern and the permutation separately.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem permutedLightWord_eq_iff
    (T : Finset (Site m n)) (ell : ℕ)
    (p q : BlockPattern T ell)
    (pi sigma : Equiv.Perm (Fin ell)) :
    permutedLightWord T ell p pi = permutedLightWord T ell q sigma ↔
      p = q ∧ pi = sigma := by
  constructor
  · intro hword
    have hlight : p.1.light = q.1.light := by
      ext s
      rw [canonicalLightWord_surjective T ell p s,
        canonicalLightWord_surjective T ell q s]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨sigma (pi.symm k), ?_⟩
        have hkword := congrFun hword (pi.symm k)
        simpa [permutedLightWord, hk] using hkword.symm
      · rintro ⟨k, hk⟩
        refine ⟨pi (sigma.symm k), ?_⟩
        have hkword := congrFun hword (sigma.symm k)
        simpa [permutedLightWord, hk] using hkword
    have hpqVal : p.1 = q.1 :=
      pattern_eq_of_light_heavy_eq hlight (p.2.1.trans q.2.1.symm)
    have hpq : p = q := Subtype.ext hpqVal
    subst q
    have hpi : pi = sigma := by
      apply Equiv.ext
      intro k
      exact canonicalLightWord_injective T ell p
        (congrFun hword k)
    exact ⟨rfl, hpi⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Include the external coordinate and an ordered light support in the
literal labelled-particle basis.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def blockLabel (T : Finset (Site m n)) (ell : ℕ)
    (x : BlockIndex d T ell) (pi : Equiv.Perm (Fin ell)) :
    LabelledIndex d m n ell :=
  (x.1, permutedLightWord T ell x.2 pi)

/-- Relabelling a block label composes its enumeration permutation.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem relabelSlots_blockLabel
    (T : Finset (Site m n)) (ell : ℕ)
    (rho pi : Equiv.Perm (Fin ell)) (x : BlockIndex d T ell) :
    relabelSlots rho (blockLabel T ell x pi) =
      blockLabel T ell x (rho.trans pi) := by
  rfl

/-- Block labels agree exactly when their block coordinates and permutations agree.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem blockLabel_eq_iff (T : Finset (Site m n)) (ell : ℕ)
    (x y : BlockIndex d T ell) (pi sigma : Equiv.Perm (Fin ell)) :
    blockLabel T ell x pi = blockLabel T ell y sigma ↔
      x = y ∧ pi = sigma := by
  constructor
  · intro h
    have ha : x.1 = y.1 :=
      congrArg (fun z : LabelledIndex d m n ell ↦ z.1) h
    have hw : permutedLightWord T ell x.2 pi =
        permutedLightWord T ell y.2 sigma :=
      congrArg (fun z : LabelledIndex d m n ell ↦ z.2) h
    obtain ⟨hp, hpi⟩ := (permutedLightWord_eq_iff T ell x.2 y.2 pi sigma).mp hw
    exact ⟨Prod.ext ha hp, hpi⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The permutation count is the cardinality of the finite slot-permutation group.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def permutationCount (ell : ℕ) : ℕ :=
  Fintype.card (Equiv.Perm (Fin ell))

/-- The slot-permutation count is strictly positive, also for zero slots.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem permutationCount_pos (ell : ℕ) : 0 < permutationCount ell := by
  exact Fintype.card_pos

/-- Composition with a fixed inverse permutation is a permutation of the slot-permutation group.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def relativePermEquiv (pi : Equiv.Perm (Fin ell)) :
    Equiv.Perm (Fin ell) ≃ Equiv.Perm (Fin ell) where
  toFun sigma := pi.symm.trans sigma
  invFun tau := pi.trans tau
  left_inv sigma := by
    apply Equiv.ext
    intro k
    simp
  right_inv tau := by
    apply Equiv.ext
    intro k
    simp

/-- A two-permutation labelled matrix entry depends only on the relative permutation.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem labelledG_blockLabel_relative
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (x y : BlockIndex d T ell)
    (pi sigma : Equiv.Perm (Fin ell)) :
    labelledG F ell (blockLabel T ell x pi) (blockLabel T ell y sigma) =
      labelledG F ell
        (blockLabel T ell x (Equiv.refl (Fin ell)))
        (blockLabel T ell y (pi.symm.trans sigma)) := by
  calc
    labelledG F ell (blockLabel T ell x pi) (blockLabel T ell y sigma) =
        labelledG F ell
          (relabelSlots pi.symm (blockLabel T ell x pi))
          (relabelSlots pi.symm (blockLabel T ell y sigma)) :=
      (labelledG_relabelSlots F ell pi.symm _ _).symm
    _ = _ := by simp

/-- Summing over both label permutations gives the permutation count times the relative-permutation sum.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem sum_sum_labelledG_blockLabel
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (x y : BlockIndex d T ell) :
    (∑ pi, ∑ sigma,
      labelledG F ell (blockLabel T ell x pi) (blockLabel T ell y sigma)) =
      (permutationCount ell : ℝ) *
        ∑ tau, labelledG F ell
          (blockLabel T ell x (Equiv.refl (Fin ell)))
          (blockLabel T ell y tau) := by
  calc
    (∑ pi : Equiv.Perm (Fin ell), ∑ sigma : Equiv.Perm (Fin ell),
      labelledG F ell (blockLabel T ell x pi) (blockLabel T ell y sigma)) =
        ∑ pi : Equiv.Perm (Fin ell), ∑ sigma : Equiv.Perm (Fin ell), labelledG F ell
          (blockLabel T ell x (Equiv.refl (Fin ell)))
          (blockLabel T ell y (pi.symm.trans sigma)) := by
      apply Finset.sum_congr rfl
      intro pi _hpi
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      exact labelledG_blockLabel_relative F T ell x y pi sigma
    _ = ∑ pi : Equiv.Perm (Fin ell), ∑ tau : Equiv.Perm (Fin ell), labelledG F ell
          (blockLabel T ell x (Equiv.refl (Fin ell)))
          (blockLabel T ell y tau) := by
      apply Finset.sum_congr rfl
      intro pi _hpi
      exact Equiv.sum_comp (relativePermEquiv pi)
        (fun tau ↦ labelledG F ell
          (blockLabel T ell x (Equiv.refl (Fin ell)))
          (blockLabel T ell y tau))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        permutationCount]

/-- The real coordinate delta equals one on equal indices and zero otherwise.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def coordinateDelta {I : Type*} [DecidableEq I] (x y : I) : ℝ :=
  if x = y then 1 else 0

/-- Summing a product of coordinate deltas contracts to one coordinate delta.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem sum_coordinateDelta_mul_coordinateDelta
    {I : Type*} [Fintype I] [DecidableEq I] (x y : I) :
    (∑ z, coordinateDelta z x * coordinateDelta z y) =
      coordinateDelta x y := by
  by_cases hxy : x = y
  · subst y
    simp [coordinateDelta]
  · simp [coordinateDelta, hxy, Ne.symm hxy]

end NLAlib.SparseFock.LightSectorConcrete
