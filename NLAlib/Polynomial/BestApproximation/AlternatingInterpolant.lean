import NLAlib.Polynomial.BestApproximation.AlternationLowerBound

/-!
# Interpolation nodes from alternating errors

An error alternating at `n+2` ordered samples has `n+1` distinct interior zeros, and the
certificate polynomial is the Lagrange interpolant of the target at these zeros.
Source: Trefethen, ATAP, Exercise 10.12.
Atlas: `best-approximant-interpolates` (the step after the alternation theorem).
-/

noncomputable section

open Polynomial

namespace NLAlib

/-- The zeros between alternating errors are distinct interior interpolation nodes.
Source: Trefethen, ATAP, Exercise 10.12. This isolates the intermediate-value step, with
an alternating sample certificate as the hypothesis.
atlas: best-approximant-interpolates (partial) -/
theorem exists_interpolate_eq_of_alternation {n : ℕ} {a b : ℝ} (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) {p : ℝ[X]} (hp : p.degree ≤ n)
    {v : Fin (n + 2) → ℝ} (hv : StrictMono v) (hvab : ∀ i, v i ∈ Set.Icc a b)
    (hsign : ∀ i : Fin (n + 1),
      (f (v i.castSucc) - p.eval (v i.castSucc)) *
        (f (v i.succ) - p.eval (v i.succ)) < 0) :
    ∃ c : Fin (n + 1) → ℝ, StrictMono c ∧ (∀ i, c i ∈ Set.Ioo a b) ∧
      (∀ i, f (c i) = p.eval (c i)) ∧
      Lagrange.interpolate Finset.univ c (f ∘ c) = p := by
  have hsub : Set.Icc (v 0) (v (Fin.last _)) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc (hvab 0).1 (hvab _).2
  obtain ⟨c, hc, hczero⟩ := exists_strictMono_eq_zero_of_mul_neg hv
    ((hf.sub p.continuous.continuousOn).mono hsub) hsign
  have hcval : ∀ i, f (c i) = p.eval (c i) := fun i => sub_eq_zero.mp (hczero i).2
  refine ⟨c, hc, fun i => ?_, hcval, ?_⟩
  · exact ⟨(hvab i.castSucc).1.trans_lt (hczero i).1.1,
      (hczero i).1.2.trans_le (hvab i.succ).2⟩
  · apply (Lagrange.eq_interpolate_of_eval_eq (f ∘ c) hc.injective.injOn ?_ ?_).symm
    · rw [Finset.card_univ, Fintype.card_fin]
      exact hp.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
    · intro i _; exact (hcval i).symm

end NLAlib
