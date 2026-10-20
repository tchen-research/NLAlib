import NLAlib.Probability.Free.WordFields
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.List.Chain

/-!
# Exact Chebyshev word creation and alternating vacuum moments

The native rescaled second-kind Chebyshev polynomial `S_n` evaluated at a
concrete left field prepends `n` copies of its letter to any word whose first
letter differs from that field. Hence every nonempty alternating product of
positive-degree Chebyshev blocks has zero actual vacuum expectation.

This is a finite algebraic freeness-basis bridge. Extending from these blocks
to all centered polynomials or closed single-generator algebras is separate;
no free-family predicate or semicircular law is assumed or asserted here.

Source: Nica--Speicher, Lectures on the Combinatorics of Free Probability,
the full-Fock realization of Propositions 7.15--7.18.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct

namespace NLAlib

variable {ι : Type*}

private theorem wordAnnihilation_apply_single_eq_zero_of_head?_ne
    (i : ι) (w : List ι) (hhead : w.head? ≠ some i) (z : ℂ) :
    wordAnnihilation i (lp.single 2 w z) = 0 := by
  cases w with
  | nil => simp
  | cons j w =>
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hhead rfl
    simp [hij]

/-- A native rescaled Chebyshev polynomial in an actual word field creates
exactly its degree many copies of that letter on every different-head word.
The empty input word and degree zero are included. -/
theorem aeval_chebyshevS_wordField_apply_single
    (i : ι) (w : List ι) (hhead : w.head? ≠ some i) (n : ℕ) (z : ℂ) :
    (Polynomial.aeval (wordField i) (Polynomial.Chebyshev.S ℂ (n : ℤ)))
        (lp.single 2 w z) = lp.single 2 (List.replicate n i ++ w) z := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp [wordField, LinearIsometry.coe_toContinuousLinearMap,
      wordAnnihilation_apply_single_eq_zero_of_head?_ne i w hhead z]
  | more n hn hn1 =>
    have hRec : Polynomial.Chebyshev.S ℂ ((n + 2 : ℕ) : ℤ) =
        Polynomial.X * Polynomial.Chebyshev.S ℂ ((n + 1 : ℕ) : ℤ) -
          Polynomial.Chebyshev.S ℂ (n : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        Polynomial.Chebyshev.S_add_two ℂ (n : ℤ)
    rw [hRec, map_sub, map_mul, Polynomial.aeval_X]
    simp only [sub_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hn, hn1]
    simp [wordField, LinearIsometry.coe_toContinuousLinearMap,
      List.replicate_succ, List.cons_append]

/-- The native Chebyshev polynomial of a concrete field sends the actual
vacuum to its repeated-letter unit basis vector. -/
theorem aeval_chebyshevS_wordField_apply_wordVacuum (i : ι) (n : ℕ) :
    (Polynomial.aeval (wordField i) (Polynomial.Chebyshev.S ℂ (n : ℤ))) (wordVacuum ι) =
      lp.single 2 (List.replicate n i) 1 := by
  simpa only [wordVacuum, List.append_nil] using
    aeval_chebyshevS_wordField_apply_single i [] (by simp) n 1

/-- Every positive-degree native Chebyshev block is actually centered under
the concrete vacuum functional; degree zero has expectation one. -/
theorem wordVacuumExpectation_aeval_chebyshevS_wordField (i : ι) (n : ℕ) :
    wordVacuumExpectation ι
        (Polynomial.aeval (wordField i) (Polynomial.Chebyshev.S ℂ (n : ℤ))) =
      if n = 0 then 1 else 0 := by
  rw [wordVacuumExpectation_apply, aeval_chebyshevS_wordField_apply_wordVacuum]
  by_cases hn : n = 0
  · simp [hn, wordVacuum]
  · simp [wordVacuum, lp.inner_single_left, lp.single_apply, hn]

/-- An alternating list of positive-degree actual Chebyshev blocks sends
the vacuum to the unit word formed by concatenating the repeated letters.
This exact operator identity includes the empty block list. -/
theorem list_prod_aeval_chebyshevS_wordField_apply_wordVacuum
    (blocks : List (ι × ℕ)) (hpos : ∀ b ∈ blocks, 0 < b.2)
    (hchain : blocks.IsChain (fun b c => b.1 ≠ c.1)) :
    ((blocks.map (fun b => Polynomial.aeval (wordField b.1)
        (Polynomial.Chebyshev.S ℂ (b.2 : ℤ)))).prod) (wordVacuum ι) =
      lp.single 2 (blocks.flatMap (fun b => List.replicate b.2 b.1)) 1 := by
  induction blocks with
  | nil => simp [wordVacuum]
  | cons b blocks ih =>
    rcases b with ⟨i, n⟩
    have hposTail : ∀ b ∈ blocks, 0 < b.2 := fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have hchainTail : blocks.IsChain (fun b c => b.1 ≠ c.1) := hchain.tail
    rw [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, ih hposTail hchainTail]
    have hhead : (blocks.flatMap (fun b => List.replicate b.2 b.1)).head? ≠ some i := by
      cases blocks with
      | nil => simp
      | cons b blocks =>
        rcases b with ⟨j, m⟩
        have hm : 0 < m := hposTail (j, m) (by simp)
        have hij : i ≠ j := (List.isChain_cons_cons.mp hchain).1
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
        simpa only [List.flatMap_cons, List.replicate_succ, List.cons_append,
          List.head?_cons, ne_eq, Option.some.injEq] using hij.symm
    simpa only [List.flatMap_cons] using
      aeval_chebyshevS_wordField_apply_single i _ hhead n 1

/-- Every nonempty alternating product of positive-degree native Chebyshev
blocks has zero actual vacuum expectation. This proves the centered alternating
moment identity for the concrete Chebyshev basis, with no independence premise. -/
theorem wordVacuumExpectation_list_prod_aeval_chebyshevS_wordField_eq_zero
    (blocks : List (ι × ℕ)) (hne : blocks ≠ [])
    (hpos : ∀ b ∈ blocks, 0 < b.2)
    (hchain : blocks.IsChain (fun b c => b.1 ≠ c.1)) :
    wordVacuumExpectation ι ((blocks.map (fun b => Polynomial.aeval (wordField b.1)
      (Polynomial.Chebyshev.S ℂ (b.2 : ℤ)))).prod) = 0 := by
  rw [wordVacuumExpectation_apply,
    list_prod_aeval_chebyshevS_wordField_apply_wordVacuum blocks hpos hchain]
  cases blocks with
  | nil => exact (hne rfl).elim
  | cons b blocks =>
    rcases b with ⟨i, n⟩
    have hn : 0 < n := hpos (i, n) (by simp)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [wordVacuum, List.flatMap_cons, List.replicate_succ,
      lp.inner_single_left, lp.single_apply]

end NLAlib
