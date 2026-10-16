import NLAlib.Polynomial.BestApproximation.OddMinimaxInterval
/-!+# Greedy odd minimax updates on their actual successive interval images

The sequence predicate records genuine uniform minimization at each step
and the attained minimum and maximum of the actual interval image. It
contains no assumed rate, normalization or contraction certificate.
-/
noncomputable section
open Set
namespace NLAlib

/-- A genuine greedy minimax sequence in the supplied scalar coefficients.
The bounds and their attainment characterize the true extrema of each
continuous interval image. -/
structure IsGreedyOddMinimax (q : ℕ) (ell : ℝ) (c : ℕ → ℕ → ℝ) (l u : ℕ → ℝ) : Prop where
  lower_zero : l 0 = ell
  upper_zero : u 0 = 1
  minimax : ∀ k, IsOddMinimaxOn q (c k) (l k) (u k)
  bounds : ∀ k x, x ∈ Icc (l k) (u k) →
    l (k + 1) ≤ oddScalarUpdate q (c k) x ∧ oddScalarUpdate q (c k) x ≤ u (k + 1)
  attain_lower : ∀ k, ∃ x ∈ Icc (l k) (u k), oddScalarUpdate q (c k) x = l (k + 1)
  attain_upper : ∀ k, ∃ x ∈ Icc (l k) (u k), oddScalarUpdate q (c k) x = u (k + 1)

/-- Every successive actual image remains a positive interval, even if
it collapses to the singleton `{1}`. -/
theorem IsGreedyOddMinimax.positive_intervals {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (k : ℕ) : 0 < l k ∧ l k ≤ u k := by
  induction k with
  | zero => simpa only [h.lower_zero, h.upper_zero] using And.intro hell hell1
  | succ k ih =>
    have hh := (h.minimax k).interval_image_normalized ih.1 ih.2
      (h.bounds k) (h.attain_lower k) (h.attain_upper k)
    exact ⟨hh.1, hh.2.1⟩

/-- Actual interval images are centered at one; their lower endpoint
therefore records the genuine uniform minimax error. -/
theorem IsGreedyOddMinimax.normalized_images {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (k : ℕ) :
    l (k + 1) + u (k + 1) = 2 ∧ oddUniformError q (c k) (l k) (u k) = 1 - l (k + 1) := by
  have hi := h.positive_intervals hell hell1 k
  exact ((h.minimax k).interval_image_normalized hi.1 hi.2
    (h.bounds k) (h.attain_lower k) (h.attain_upper k)).2.2

/-- Every intermediate scalar iterate lies in the actual interval used
by the next minimax problem. -/
theorem IsGreedyOddMinimax.composition_mem_interval {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    {x : ℝ} (hx : x ∈ Icc ell 1) (k : ℕ) :
    oddScalarComposition q c x k ∈ Icc (l k) (u k) := by
  induction k with
  | zero => simpa only [oddScalarComposition, h.lower_zero, h.upper_zero] using hx
  | succ k ih => exact h.bounds k _ ih

end NLAlib
