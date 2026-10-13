import NLAlib.Polynomial.BestApproximation.MinimaxError
import NLAlib.ForMathlib.Topology.Order.IntermediateValue

/-!
# Alternation certificates for polynomial approximation

The de la Vallée Poussin certificate is discrete: a competitor beating the smallest
alternating error would make its difference from the certificate polynomial have too many
roots. No continuity of the target function is needed for this assertion.
Source: Cheney (1966), Chapter 3; Trefethen, ATAP, Exercise 10.3.
Atlas: `de-la-vallee-poussin`.
-/

noncomputable section

open Polynomial

namespace NLAlib

/-- A nonzero polynomial of degree at most `n` cannot alternate strictly in sign at
`n+2` ordered points. Source: Cheney (1966), Chapter 3, the root-counting step of
the de la Vallée Poussin theorem. -/
theorem not_forall_eval_mul_eval_neg_of_degree_le {n : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ n) {v : Fin (n + 2) → ℝ} (hv : StrictMono v) :
    ¬ ∀ i : Fin (n + 1), p.eval (v i.castSucc) * p.eval (v i.succ) < 0 := by
  intro hsign
  obtain ⟨c, hc, hczero⟩ := exists_strictMono_eq_zero_of_mul_neg hv
    p.continuous.continuousOn hsign
  have hpzero : p = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (s := Finset.univ) (v := c) hc.injective.injOn
    · rw [Finset.card_univ, Fintype.card_fin]
      exact hp.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
    · intro i _; exact (hczero i).2
  simpa [hpzero] using hsign 0

/-- A polynomial error alternating at `n+2` ordered points certifies a lower error bound
for every degree-`n` competitor. Source: Cheney (1966), Chapter 3; ATAP, Exercise 10.3.
The target function can be completely arbitrary, and `ε` is any common lower bound on
the absolute values of the alternating errors.
atlas: de-la-vallee-poussin -/
theorem exists_abs_sub_eval_ge_of_alternation {n : ℕ} (f : ℝ → ℝ) {p : ℝ[X]}
    (hp : p.degree ≤ n) {v : Fin (n + 2) → ℝ} (hv : StrictMono v)
    (hsign : ∀ i : Fin (n + 1),
      (f (v i.castSucc) - p.eval (v i.castSucc)) *
        (f (v i.succ) - p.eval (v i.succ)) < 0)
    {ε : ℝ} (hε : ∀ i, ε ≤ |f (v i) - p.eval (v i)|)
    (q : ℝ[X]) (hq : q.degree ≤ n) :
    ∃ i, ε ≤ |f (v i) - q.eval (v i)| := by
  by_contra! hbeat
  have hd : (q - p).degree ≤ n := (degree_sub_le q p).trans (max_le hq hp)
  apply not_forall_eval_mul_eval_neg_of_degree_le hd hv
  intro i
  have hi := mul_sub_mul_sub_neg_of_abs_lt (hsign i)
    ((hbeat i.castSucc).trans_le (hε i.castSucc))
    ((hbeat i.succ).trans_le (hε i.succ))
  simpa only [eval_sub, sub_sub_sub_cancel_left] using hi

/-- A polynomial with alternating sample errors certifies a lower bound on the minimax
error on any compact real domain. Source: Cheney (1966), Chapter 3; ATAP, Exercise 10.3.
atlas: de-la-vallee-poussin -/
theorem le_minimaxError_of_alternation {s : Set ℝ} [CompactSpace s] {n : ℕ}
    (f : C(s, ℝ)) {p : ℝ[X]} (hp : p.degree ≤ n) {v : Fin (n + 2) → s}
    (hv : StrictMono (fun i => (v i : ℝ)))
    (hsign : ∀ i : Fin (n + 1),
      (f (v i.castSucc) - p.eval (v i.castSucc : ℝ)) *
        (f (v i.succ) - p.eval (v i.succ : ℝ)) < 0)
    {ε : ℝ} (hε : ∀ i, ε ≤ |f (v i) - p.eval (v i : ℝ)|) :
    ε ≤ minimaxError n f := by
  classical
  let g : ℝ → ℝ := fun x => if hx : x ∈ s then f ⟨x, hx⟩ else 0
  have hgv : ∀ i, g (v i) = f (v i) := by intro i; simp [g, (v i).property]
  obtain ⟨q, hq, hbest⟩ := exists_degree_le_norm_sub_eq_minimaxError n f
  obtain ⟨i, hi⟩ := exists_abs_sub_eval_ge_of_alternation g hp hv
    (by simpa only [hgv] using hsign) (by simpa only [hgv] using hε) q hq
  rw [hgv] at hi
  have hnorm := (f - q.toContinuousMapOn s).norm_coe_le_norm (v i)
  rw [hbest] at hnorm
  exact hi.trans hnorm

end NLAlib
