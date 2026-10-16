import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! # Finite Hermite occupation indices

The degree cutoff is on total occupation. Coordinate raising and lowering
remain concrete functions on finite indices, including at the cutoff.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
open Finset
namespace NLAlib

/-- Multiindices of total degree at most `p`. The zero multiindex is included
even when the coordinate type is empty. -/
def HermiteIndex (ι : Type*) [Fintype ι] (p : ℕ) :=
  {a : ι → ℕ // ∑ i, a i ≤ p}

namespace HermiteIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

/-- The occupation number at one coordinate is at most the total cutoff. -/
theorem coordinate_le (a : HermiteIndex ι p) (i : ι) : a.val i ≤ p :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans a.property

/-- The degree-bounded multiindex space is finite, by embedding it into a
finite coordinate cube. -/
instance instFintype : Fintype (HermiteIndex ι p) :=
  Fintype.ofInjective
    (fun a : HermiteIndex ι p => fun i : ι => (⟨a.val i, Nat.lt_succ_of_le (coordinate_le a i)⟩ : Fin (p + 1)))
    (by
      intro a b h
      apply Subtype.ext
      funext i
      exact congrArg Fin.val (congrFun h i))

/-- Equality of bounded multiindices is decidable. -/
instance instDecidableEq : DecidableEq (HermiteIndex ι p) :=
  inferInstanceAs (DecidableEq {a : ι → ℕ // ∑ i, a i ≤ p})

/-- The total occupation degree. -/
def degree (a : HermiteIndex ι p) : ℕ := ∑ i, a.val i

/-- The vacuum is the zero occupation multiindex. -/
def vacuum : HermiteIndex ι p := ⟨0, by simp⟩

/-- Every coordinate of the vacuum occupation is zero. -/
@[simp] theorem vacuum_val (i : ι) : (vacuum : HermiteIndex ι p).val i = 0 := rfl

/-- The vacuum has degree zero. -/
@[simp] theorem degree_vacuum : (vacuum : HermiteIndex ι p).degree = 0 := by
  simp [degree, vacuum]

/-- Lowering one coordinate never leaves the degree cutoff. -/
def lower (a : HermiteIndex ι p) (i : ι) : HermiteIndex ι p :=
  ⟨Function.update a.val i (a.val i - 1), by
    refine (Finset.sum_le_sum fun j _ => ?_).trans a.property
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]⟩

/-- Lowering changes only the selected coordinate. -/
@[simp] theorem lower_val (a : HermiteIndex ι p) (i j : ι) :
    (lower a i).val j = if j = i then a.val i - 1 else a.val j := by
  simp [lower, Function.update_apply]

/-- The lowering degree identity is valid when the coordinate is occupied. -/
theorem degree_lower (a : HermiteIndex ι p) (i : ι) (hi : 0 < a.val i) :
    (lower a i).degree + 1 = a.degree := by
  have hsum := Finset.sum_update_of_mem (Finset.mem_univ i) a.val (a.val i - 1)
  change (∑ j, Function.update a.val i (a.val i - 1) j) + 1 = ∑ j, a.val j
  rw [hsum]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  omega

/-- Raising a coordinate is defined below the total cutoff only. -/
def raise (a : HermiteIndex ι p) (i : ι) (h : a.degree < p) : HermiteIndex ι p :=
  ⟨Function.update a.val i (a.val i + 1), by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (a.val j)) (Finset.mem_univ i)
    change (∑ j, a.val j) < p at h
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)] at h
    omega⟩

/-- Raising changes only the selected coordinate. -/
@[simp] theorem raise_val (a : HermiteIndex ι p) (i j : ι) (h : a.degree < p) :
    (raise a i h).val j = if j = i then a.val i + 1 else a.val j := by
  simp [raise, Function.update_apply]

/-- Raising increases total degree by exactly one. -/
@[simp] theorem degree_raise (a : HermiteIndex ι p) (i : ι) (h : a.degree < p) :
    (raise a i h).degree = a.degree + 1 := by
  change (∑ j, Function.update a.val i (a.val i + 1) j) = (∑ j, a.val j) + 1
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (a.val j)) (Finset.mem_univ i)
  omega

/-- Lowering reverses a permitted raising step. -/
@[simp] theorem lower_raise (a : HermiteIndex ι p) (i : ι) (h : a.degree < p) :
    lower (raise a i h) i = a := by
  apply Subtype.ext
  funext j
  by_cases hij : j = i <;> simp [hij]

/-- Raising reverses an occupied lowering step, with its cutoff condition
deduced from the original degree bound. -/
theorem raise_lower (a : HermiteIndex ι p) (i : ι) (hi : 0 < a.val i)
    (h : (lower a i).degree < p) : raise (lower a i) i h = a := by
  apply Subtype.ext
  funext j
  by_cases hij : j = i
  · subst j
    simp only [raise_val, lower_val, if_true]
    omega
  · simp [hij]

/-- Lowering weakly decreases degree, whether or not the coordinate is
occupied. -/
theorem degree_lower_le (a : HermiteIndex ι p) (i : ι) : (a.lower i).degree ≤ a.degree := by
  apply Finset.sum_le_sum
  intro j _
  by_cases h : j = i
  · subst j; simp
  · simp [h]

/-- Inclusion into a larger total-degree cutoff. -/
def embed {q : ℕ} (a : HermiteIndex ι p) (h : p ≤ q) : HermiteIndex ι q :=
  ⟨a.val, a.property.trans h⟩

/-- Cutoff inclusion preserves coordinate values. -/
@[simp] theorem embed_val {q : ℕ} (a : HermiteIndex ι p) (h : p ≤ q) (i : ι) :
    (a.embed h).val i = a.val i := rfl

/-- Cutoff inclusion preserves total degree. -/
@[simp] theorem degree_embed {q : ℕ} (a : HermiteIndex ι p) (h : p ≤ q) :
    (a.embed h).degree = a.degree := rfl

/-- Cutoff inclusion is injective. -/
theorem embed_injective {q : ℕ} (h : p ≤ q) :
    Function.Injective (fun a : HermiteIndex ι p => a.embed h) := by
  intro a b he
  apply Subtype.ext
  exact congrArg (fun c : HermiteIndex ι q => c.val) he

/-- Raising a bounded occupation into the next cutoff is always permitted. -/
def raiseNext (a : HermiteIndex ι p) (i : ι) : HermiteIndex ι (p + 1) :=
  (a.embed (Nat.le_succ p)).raise i (by
    change (∑ i, a.val i) < p + 1
    exact Nat.lt_succ_of_le a.property)

/-- The next-cutoff raising step has the literal coordinate update. -/
@[simp] theorem raiseNext_val (a : HermiteIndex ι p) (i j : ι) :
    (a.raiseNext i).val j = if j = i then a.val i + 1 else a.val j := by
  simp [raiseNext]

/-- Raising into the next cutoff increases degree by one. -/
@[simp] theorem degree_raiseNext (a : HermiteIndex ι p) (i : ι) :
    (a.raiseNext i).degree = a.degree + 1 := by
  simp [raiseNext]

/-- Lowering at a distinct coordinate commutes with an interior raising
step, including a zero occupation at the lowered coordinate. -/
theorem lower_raise_of_ne (a : HermiteIndex ι p) {i j : ι} (hij : i ≠ j)
    (h : a.degree < p) (h' : (a.lower i).degree < p) :
    (a.raise j h).lower i = (a.lower i).raise j h' := by
  apply Subtype.ext
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hki]
    · simp [hki, hkj]

end HermiteIndex
end NLAlib
