import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Explicit finite nets for real intervals

A uniform grid covers a real interval with the expected linear cardinality
bound. This is the deterministic discretization used in the spectral grid
argument of arXiv:2201.05142v3, Propositions 7.4 and 7.7.
-/

noncomputable section
set_option autoImplicit false
namespace Real

/-- An interval of radius L has an ε-net of size at most ceil(2L/ε)+1.
The grid may extend past its right endpoint, and a zero radius is allowed. -/
theorem exists_finset_interval_net (a : ℝ) {L ε : ℝ} (_hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ N : Finset ℝ, N.card ≤ ⌈2*L/ε⌉₊+1 ∧
      ∀ x : ℝ, |x-a| ≤ L → ∃ u ∈ N, |x-u| ≤ ε := by
  classical
  let q : ℕ := ⌈2*L/ε⌉₊
  let N := (Finset.range (q+1)).image (fun k : ℕ => a-L+(k : ℝ)*ε)
  refine ⟨N, (Finset.card_image_le).trans (by simp [q]), ?_⟩
  intro x hx
  have hlo : 0 ≤ x-a+L := by have hh := (abs_le.mp hx).1; linarith
  have hhi : x-a+L ≤ 2*L := by have hh := (abs_le.mp hx).2; linarith
  let k : ℕ := ⌊(x-a+L)/ε⌋₊
  have hdiv : 0 ≤ (x-a+L)/ε := div_nonneg hlo hε.le
  have hklo : (k : ℝ) ≤ (x-a+L)/ε := Nat.floor_le hdiv
  have hkhi : (x-a+L)/ε < (k : ℝ)+1 := Nat.lt_floor_add_one _
  have hkq : k ≤ q := by
    have hh : (k : ℝ) ≤ (q : ℝ) := hklo.trans
      ((div_le_div_of_nonneg_right hhi hε.le).trans (Nat.le_ceil _))
    exact_mod_cast hh
  refine ⟨a-L+(k : ℝ)*ε, Finset.mem_image.mpr
    ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hkq), rfl⟩, ?_⟩
  have hmullo : (k : ℝ)*ε ≤ x-a+L := (le_div_iff₀ hε).mp hklo
  have hmulhi : x-a+L < ((k : ℝ)+1)*ε := (div_lt_iff₀ hε).mp hkhi
  rw [abs_of_nonneg (by linarith : 0 ≤ x-(a-L+(k : ℝ)*ε))]
  linarith

/-- A finite union of intervals has a net with the sum of their grid-size
bounds. The set of centers may be empty. -/
theorem exists_finset_union_intervals_net {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ N : Finset ℝ, N.card ≤ Fintype.card ι*(⌈2*L/ε⌉₊+1) ∧
      ∀ x : ℝ, (∃ i, |x-a i| ≤ L) → ∃ u ∈ N, |x-u| ≤ ε := by
  classical
  choose N hcard hcover using (fun i => exists_finset_interval_net (a i) hL hε)
  refine ⟨Finset.univ.biUnion N, ?_, ?_⟩
  · simpa only [Finset.card_univ] using Finset.card_biUnion_le_card_mul
      Finset.univ N (⌈2*L/ε⌉₊+1) (fun i _ => hcard i)
  · intro x ⟨i, hi⟩
    obtain ⟨u, hu, hclose⟩ := hcover i x hi
    exact ⟨u, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hu⟩, hclose⟩

end Real
