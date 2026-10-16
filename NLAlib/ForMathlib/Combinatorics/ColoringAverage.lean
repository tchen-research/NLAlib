import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-!
# Counting colorings that retain an injective ordered tuple

The coordinate restriction has independent free colors outside the tuple.
This is the finite combinatorial identity underlying multilinear decoupling.
-/

noncomputable section
open scoped Classical
namespace Equiv

/-- Decompose a coloring into its values along an injective tuple and its values
outside the tuple. -/
def coloringSplit {τ ι κ : Type*} (z : τ → ι) (hz : Function.Injective z) :
    (ι → κ) ≃ (τ → κ) × ({i // i ∉ Set.range z} → κ) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Set.range z) (fun _ => κ)).trans
    ((Equiv.arrowCongr (Equiv.ofInjective z hz).symm (Equiv.refl κ)).prodCongr
      (Equiv.refl _))

/-- The first part of the coloring decomposition is ordinary restriction. -/
@[simp] theorem coloringSplit_fst {τ ι κ : Type*} (z : τ → ι)
    (hz : Function.Injective z) (c : ι → κ) (t : τ) :
    (coloringSplit z hz c).1 t = c (z t) := by
  simp [coloringSplit, Equiv.piEquivPiSubtypeProd, Equiv.arrowCongr,
    Equiv.ofInjective]

end Equiv

namespace Finset

/-- Exactly one coloring of the selected coordinates retains the ordered tuple;
the other coordinates can be colored freely. -/
theorem sum_coloring_indicator {τ ι : Type*} [Fintype τ] [Fintype ι]
    [DecidableEq τ] [DecidableEq ι]
    (z : τ → ι) (hz : Function.Injective z) :
    (∑ c : ι → τ, if ∀ t, c (z t) = t then (1 : ℕ) else 0) =
      Fintype.card ({i // i ∉ Set.range z} → τ) := by
  classical
  let e := Equiv.coloringSplit (κ := τ) z hz
  have hf (c : ι → τ) : (∀ t, c (z t) = t) ↔ (e c).1 = id := by
    constructor
    · intro h
      funext t
      simpa [e] using h t
    · intro h t
      have ht := congrFun h t
      simpa [e] using ht
  simp_rw [hf]
  rw [← e.symm.sum_comp (fun c : ι → τ => if (e c).1 = id then (1 : ℕ) else 0)]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single id]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The retained-color count multiplied by `q^q` is the total number of
colorings. This form avoids division and includes the empty tuple. -/
theorem sum_coloring_indicator_mul_card_pow {τ ι : Type*} [Fintype τ] [Fintype ι]
    [DecidableEq τ] [DecidableEq ι]
    (z : τ → ι) (hz : Function.Injective z) :
    (∑ c : ι → τ, if ∀ t, c (z t) = t then (1 : ℕ) else 0) *
      Fintype.card τ ^ Fintype.card τ = Fintype.card (ι → τ) := by
  classical
  rw [sum_coloring_indicator z hz]
  have he := Fintype.card_congr (Equiv.coloringSplit (κ := τ) z hz)
  simpa [Fintype.card_fun, Nat.mul_comm] using he.symm

end Finset
