import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

/-!
# Double counting products over one-element deletions

Every size-`k` set occurs once for each missing ambient element when deleting
one element from all size-`k+1` sets. This is the multiplicative incidence
count used in Szász's determinant inequality.
-/

noncomputable section
open scoped BigOperators
namespace NLAlib
variable {n M : Type*} [Fintype n] [DecidableEq n] [CommMonoid M]

/-- Multiplying a function over every one-element deletion of every
size-`k+1` subset counts each size-`k` subset exactly `card n-k` times.
The identity holds for every `k`, including the empty and out-of-range cases.
Horn--Johnson (2013), proof of Theorem 7.8.11; supports Szász's inequality. -/
theorem prod_powersetCard_prod_erase_eq_pow (f : Finset n → M) (k : ℕ) :
    (∏ T ∈ (Finset.univ : Finset n).powersetCard (k + 1), ∏ i ∈ T, f (T.erase i)) =
      (∏ S ∈ (Finset.univ : Finset n).powersetCard k, f S) ^ (Fintype.card n - k) := by
  classical
  let L := ((Finset.univ : Finset n).powersetCard (k + 1)).sigma (fun T => T)
  let R := ((Finset.univ : Finset n).powersetCard k).sigma (fun S => Finset.univ \ S)
  have hprod : (∏ u ∈ L, f (u.1.erase u.2)) = ∏ v ∈ R, f v.1 := by
    refine Finset.prod_bij' (fun u _ => ⟨u.1.erase u.2, u.2⟩)
      (fun v _ => ⟨insert v.2 v.1, v.2⟩) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      rcases Finset.mem_sigma.mp hu with ⟨hT, hi⟩
      have hcard := (Finset.mem_powersetCard.mp hT).2
      apply Finset.mem_sigma.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        exact ⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hi, hcard]; omega⟩
      · simp
    · intro v hv
      rcases Finset.mem_sigma.mp hv with ⟨hS, hi⟩
      have hcard := (Finset.mem_powersetCard.mp hS).2
      have hnot : v.2 ∉ v.1 := (Finset.mem_sdiff.mp hi).2
      apply Finset.mem_sigma.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        exact ⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hnot, hcard]⟩
      · exact Finset.mem_insert_self _ _
    · intro u hu
      have hi := (Finset.mem_sigma.mp hu).2
      exact Sigma.ext (Finset.insert_erase hi) (by rfl)
    · intro v hv
      have hi := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hv).2).2
      exact Sigma.ext (Finset.erase_insert hi) (by rfl)
    · intro u _
      rfl
  rw [Finset.prod_sigma', show
    (∏ x ∈ ((Finset.univ : Finset n).powersetCard (k + 1)).sigma (fun a => a), f (x.1.erase x.2)) =
      ∏ v ∈ R, f v.1 from hprod]
  rw [show R = ((Finset.univ : Finset n).powersetCard k).sigma (fun S => Finset.univ \ S) from rfl,
    Finset.prod_sigma]
  calc
    _ = ∏ S ∈ (Finset.univ : Finset n).powersetCard k, f S ^ (Fintype.card n - k) := by
      apply Finset.prod_congr rfl
      intro S hS
      change (∏ _i ∈ Finset.univ \ S, f S) = _
      rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ S),
        Finset.card_univ, (Finset.mem_powersetCard.mp hS).2]
    _ = _ := Finset.prod_pow _ _ _

end NLAlib
