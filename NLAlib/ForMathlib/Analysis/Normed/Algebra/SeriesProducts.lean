import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-!
# Ordered finite products of absolutely summable series

The finite product is the literal `List.ofFn` product, so no commutativity of
multiplication is assumed. The joint series ranges over the natural profile
space `Fin N → ℕ`. Absolute summability and the actual `HasSum` are both proved;
the empty product is included without a nonempty or norm-one assumption.
-/

noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
private theorem summable_norm_and_hasSum_list_prod
    {R : Type*} [NormedRing R] [CompleteSpace R] {N : ℕ}
    (f : Fin N → ℕ → R) (x : Fin N → R)
    (hn : ∀ j, Summable (fun m => ‖f j m‖)) (hs : ∀ j, HasSum (f j) (x j)) :
    Summable (fun m : Fin N → ℕ => ‖(List.ofFn (fun j => f j (m j))).prod‖) ∧
      HasSum (fun m : Fin N → ℕ => (List.ofFn (fun j => f j (m j))).prod)
        (List.ofFn x).prod := by
  induction N with
  | zero =>
    constructor
    · exact (hasSum_unique
        (fun m : Fin 0 → ℕ => ‖(List.ofFn (fun j => f j (m j))).prod‖)).summable
    · simpa only [List.ofFn_zero, List.prod_nil] using
        hasSum_unique (fun m : Fin 0 → ℕ => (List.ofFn (fun j => f j (m j))).prod)
  | succ N ih =>
    obtain ⟨htn, hts⟩ := ih (fun j => f j.succ) (fun j => x j.succ)
      (fun j => hn j.succ) (fun j => hs j.succ)
    let e : (ℕ × (Fin N → ℕ)) ≃ (Fin (N + 1) → ℕ) :=
      Fin.consEquiv (fun _ => ℕ)
    have hnorm : Summable (fun m : ℕ × (Fin N → ℕ) =>
        ‖f 0 m.1 * (List.ofFn (fun j => f j.succ (m.2 j))).prod‖) :=
      @Summable.mul_norm R ℕ (Fin N → ℕ) _ (f 0)
        (fun m => (List.ofFn (fun j => f j.succ (m j))).prod) (hn 0) htn
    have hprod : Summable (fun m : ℕ × (Fin N → ℕ) =>
        f 0 m.1 * (List.ofFn (fun j => f j.succ (m.2 j))).prod) := hnorm.of_norm
    have hsum : HasSum (fun m : ℕ × (Fin N → ℕ) =>
        f 0 m.1 * (List.ofFn (fun j => f j.succ (m.2 j))).prod)
        (x 0 * (List.ofFn (fun j => x j.succ)).prod) := by
      have h := hprod.hasSum
      rw [← tsum_mul_tsum_of_summable_norm (hn 0) htn, (hs 0).tsum_eq, hts.tsum_eq] at h
      exact h
    constructor
    · apply e.summable_iff.mp
      simpa only [Function.comp_def, e, Fin.consEquiv_apply,
        List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons] using hnorm
    · apply e.hasSum_iff.mp
      simpa only [Function.comp_def, e, Fin.consEquiv_apply,
        List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons] using hsum

/-- A literal finite ordered product of absolutely summable normed-ring series
is absolutely summable over its full profile space. Complete normed rings are
sufficient; multiplicative commutativity and norm one are not required. -/
theorem summable_norm_list_prod_of_summable_norm
    {R : Type*} [NormedRing R] [CompleteSpace R] {N : ℕ}
    (f : Fin N → ℕ → R) (hn : ∀ j, Summable (fun m => ‖f j m‖)) :
    Summable (fun m : Fin N → ℕ => ‖(List.ofFn (fun j => f j (m j))).prod‖) :=
  (summable_norm_and_hasSum_list_prod f (fun j => ∑' m, f j m) hn
    (fun j => (hn j).of_norm.hasSum)).1

/-- The sum of the actual profile series is the finite product of the actual
individual series sums, in their original `Fin` order. This is a genuine
`HasSum`, with joint absolute summability supplied by the preceding theorem. -/
theorem hasSum_list_prod_of_summable_norm
    {R : Type*} [NormedRing R] [CompleteSpace R] {N : ℕ}
    (f : Fin N → ℕ → R) (x : Fin N → R)
    (hs : ∀ j, HasSum (f j) (x j)) (hn : ∀ j, Summable (fun m => ‖f j m‖)) :
    HasSum (fun m : Fin N → ℕ => (List.ofFn (fun j => f j (m j))).prod)
      (List.ofFn x).prod :=
  (summable_norm_and_hasSum_list_prod f x hn hs).2
