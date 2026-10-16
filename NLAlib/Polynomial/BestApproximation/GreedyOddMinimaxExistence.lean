import NLAlib.Polynomial.BestApproximation.GreedyOddMinimax

/-! # Existence of genuine greedy odd minimax sequences

Choose an actual uniform minimizer at each positive interval and take the
attained extrema of its actual image. Positivity of normalized minimax
images permits this construction for every stage, including singleton
intervals. No convergence or contraction hypothesis enters the construction.
Source: Polar Express, §3; finite-dimensional minimax existence.
-/
noncomputable section
open Set
namespace NLAlib

private abbrev PositiveInterval := {p : ℝ × ℝ // 0 < p.1 ∧ p.1 ≤ p.2}

private structure GreedyOddStep (q : ℕ) (I : PositiveInterval) where
  coefficients : ℕ → ℝ
  next : PositiveInterval
  minimax : IsOddMinimaxOn q coefficients I.val.1 I.val.2
  bounds : ∀ x ∈ Icc I.val.1 I.val.2,
    next.val.1 ≤ oddScalarUpdate q coefficients x ∧ oddScalarUpdate q coefficients x ≤ next.val.2
  attain_lower : ∃ x ∈ Icc I.val.1 I.val.2, oddScalarUpdate q coefficients x = next.val.1
  attain_upper : ∃ x ∈ Icc I.val.1 I.val.2, oddScalarUpdate q coefficients x = next.val.2

private theorem nonempty_greedyOddStep (q : ℕ) (I : PositiveInterval) :
    Nonempty (GreedyOddStep q I) := by
  obtain ⟨c, hc⟩ := exists_isOddMinimaxOn q I.val.1 I.val.2
  obtain ⟨m, M, hb, hm, hM⟩ := exists_oddScalarUpdate_interval_bounds q c I.property.2
  have hn := hc.interval_image_normalized I.property.1 I.property.2 hb hm hM
  exact ⟨⟨c, ⟨(m, M), hn.1, hn.2.1⟩, hc, hb, hm, hM⟩⟩

/-- Actual arbitrary-length greedy minimax sequences exist from every positive
initial interval `[ell,1]`, including the singleton endpoint `ell=1`.
Every recorded interval endpoint is attained by the corresponding actual
coefficient-defined polynomial; no rate certificate is assumed.
Source: Polar Express, §3; finite-dimensional minimax existence.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem exists_isGreedyOddMinimax (q : ℕ) {ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1) :
    ∃ (c : ℕ → ℕ → ℝ) (l u : ℕ → ℝ), IsGreedyOddMinimax q ell c l u := by
  classical
  let chooseStep : (I : PositiveInterval) → GreedyOddStep q I :=
    fun I => Classical.choice (nonempty_greedyOddStep q I)
  let initial : PositiveInterval := ⟨(ell, 1), hell, hell1⟩
  let intervals : ℕ → PositiveInterval :=
    Nat.rec initial (fun _ I => (chooseStep I).next)
  let c : ℕ → ℕ → ℝ := fun k => (chooseStep (intervals k)).coefficients
  let l : ℕ → ℝ := fun k => (intervals k).val.1
  let u : ℕ → ℝ := fun k => (intervals k).val.2
  refine ⟨c, l, u, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (chooseStep (intervals k)).minimax
  · intro k x hx
    exact (chooseStep (intervals k)).bounds x hx
  · intro k
    exact (chooseStep (intervals k)).attain_lower
  · intro k
    exact (chooseStep (intervals k)).attain_upper

end NLAlib
