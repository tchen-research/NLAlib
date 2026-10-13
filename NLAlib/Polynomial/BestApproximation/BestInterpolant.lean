import NLAlib.Polynomial.BestApproximation.Equioscillation
import NLAlib.Polynomial.BestApproximation.AlternatingInterpolant

/-!
# Every best polynomial is an interpolant

The alternating extrema of a positive-error best polynomial enclose `n+1` distinct
interior interpolation points. With zero error any `n+1` distinct interior points work.
Source: Trefethen, ATAP, Exercise 10.12.
Atlas: `best-approximant-interpolates`.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

/-- Every best degree-`n` uniform polynomial approximant interpolates the target at `n+1`
distinct interior points. Source: Trefethen, ATAP, Exercise 10.12. Generalized from
`[-1,1]` to every nondegenerate real interval; the zero-error case is included.
atlas: best-approximant-interpolates -/
theorem exists_interpolate_eq_of_norm_sub_eq_minimaxError {n : ℕ} {a b : ℝ}
    (hab : a < b) (f : C(Icc a b, ℝ)) {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : ‖f - p.toContinuousMapOn (Icc a b)‖ = minimaxError n f) :
    ∃ c : Fin (n + 1) → Ioo a b, StrictMono (fun i => (c i : ℝ)) ∧
      (∀ i, f ⟨c i, Ioo_subset_Icc_self (c i).property⟩ = p.eval (c i : ℝ)) ∧
      Lagrange.interpolate Finset.univ (fun i => (c i : ℝ))
        (fun i => f ⟨c i, Ioo_subset_Icc_self (c i).property⟩) = p := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  by_cases hE : ‖f - p.toContinuousMapOn (Icc a b)‖ = 0
  · have hden : (0 : ℝ) < n + 2 := by positivity
    let c : Fin (n + 1) → Ioo a b := fun i =>
      ⟨a + (b - a) * ((i : ℕ) + 1) / (n + 2), by
        have hinum : (0 : ℝ) < (i : ℕ) + 1 := by positivity
        have hi : ((i : ℕ) + 1 : ℝ) < n + 2 := by exact_mod_cast (show (i : ℕ) + 1 < n + 2 by omega)
        constructor
        · exact lt_add_of_pos_right a (div_pos (mul_pos (sub_pos.mpr hab) hinum) hden)
        · have hpart : (b - a) * ((i : ℕ) + 1) / (n + 2) < b - a :=
            (div_lt_iff₀ hden).mpr (mul_lt_mul_of_pos_left hi (sub_pos.mpr hab))
          linarith⟩
    have hval : ∀ i, f ⟨c i, Ioo_subset_Icc_self (c i).property⟩ = p.eval (c i : ℝ) := by
      intro i
      have hzero := norm_eq_zero.mp hE
      have hi := congrArg (fun g : C(Icc a b, ℝ) =>
        g ⟨c i, Ioo_subset_Icc_self (c i).property⟩) hzero
      exact sub_eq_zero.mp hi
    have hc : StrictMono (fun i => (c i : ℝ)) := by
      intro i j hij
      have hijR : ((i : ℕ) + 1 : ℝ) < (j : ℕ) + 1 := by exact_mod_cast (show (i : ℕ) + 1 < (j : ℕ) + 1 by omega)
      have hdiv := div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left hijR (sub_pos.mpr hab)) hden
      dsimp [c]; linarith
    refine ⟨c, hc, hval, ?_⟩
    apply (Lagrange.eq_interpolate_of_eval_eq _ hc.injective.injOn ?_ ?_).symm
    · rw [Finset.card_univ, Fintype.card_fin]
      exact hp.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
    · intro i _; exact (hval i).symm
  · have hEpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE)
    obtain ⟨v, hv, _, hsign⟩ :=
      exists_alternating_extrema_of_norm_sub_eq_minimaxError hab f hp hbest hEpos
    let g : C(ℝ, ℝ) := ContinuousMap.IccExtendCM f
    have hgv : ∀ i, g (v i) = f (v i) := fun i =>
      ContinuousMap.IccExtendCM_of_mem (v i).property
    obtain ⟨c, hc, hcI, hcval, hcinterp⟩ := exists_interpolate_eq_of_alternation g
      g.continuous.continuousOn hp hv (fun i => (v i).property)
      (by simpa only [hgv] using hsign)
    let w : Fin (n + 1) → Ioo a b := fun i => ⟨c i, hcI i⟩
    have hgval : ∀ i, g (c i) = f ⟨w i, Ioo_subset_Icc_self (w i).property⟩ :=
      fun i => ContinuousMap.IccExtendCM_of_mem (Ioo_subset_Icc_self (hcI i))
    refine ⟨w, hc, ?_, ?_⟩
    · intro i; rw [← hgval]; exact hcval i
    · simpa only [Function.comp_def, hgval] using hcinterp

end NLAlib
