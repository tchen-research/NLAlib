import NLAlib.Matrix.Functions.FrameSparsificationParameters
import NLAlib.Matrix.Functions.SparseFrameCompactness

/-!
# Spectral sparsification of an identity decomposition

Every finite identity decomposition in positive dimension admits nonnegative
weights supported on at most `d * card n` atoms, with lower spectral bound `1`
and upper bound `(d + 1 + 2 * √d) / (d + 1 - 2 * √d)`, for every real `d > 1`.

Source: Batson--Spielman--Srivastava, *Twice-Ramanujan Sparsifiers* (2008),
Theorem 3.1 and Section 3.2,
[arXiv:0808.0163](https://arxiv.org/abs/0808.0163).

The integer-budget barrier theorem is applied to increasingly many disjoint
copies of the frame. A support pigeonhole argument extracts one copy with
the original support budget. Compactness then gives the exact real parameter.
-/

noncomputable section

open scoped Matrix BigOperators MatrixOrder
open Filter

namespace NLAlib

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n] [Nonempty n]

/-- An identity decomposition admits a sparse nonnegative reweighting for every
real `d > 1`. The support has cardinality at most `d * card n`, the weighted
Gram sum is at least the identity, and its upper spectral bound is
`(d + 1 + 2 * √d) / (d + 1 - 2 * √d)`.

Source: Batson--Spielman--Srivastava (2008), Theorem 3.1.
atlas: deterministic-rank-one-sparsification -/
theorem exists_nonneg_weights_spectral_sandwich
    (v : I → n → ℝ)
    (hframe : ∑ i, Matrix.vecMulVec (v i) (v i) = 1)
    (d : ℝ) (hd : 1 < d) :
    ∃ s : I → ℝ,
      (∀ i, 0 ≤ s i) ∧
      ((Function.support s).ncard : ℝ) ≤ d * (Fintype.card n : ℝ) ∧
      ((1 : Matrix n n ℝ) ≤ ∑ i, s i • Matrix.vecMulVec (v i) (v i)) ∧
      (∑ i, s i • Matrix.vecMulVec (v i) (v i) ≤
        ((d + 1 + 2 * Real.sqrt d) / (d + 1 - 2 * Real.sqrt d)) •
          (1 : Matrix n n ℝ)) := by
  classical
  let N : ℕ := Fintype.card n
  have hN : 0 < N := Fintype.card_pos
  let k : ℕ := Nat.floor (d * (N : ℝ))
  obtain ⟨r, q, hbudget, hratio⟩ := exists_nat_budget_ratio_tendsto N hN d hd
  let beta : ℕ → ℝ := fun m =>
    rankOneSparsificationFactor ((q m : ℝ) / ((N : ℝ) * (r m : ℝ)))
  have hbeta : Tendsto beta atTop (nhds (rankOneSparsificationFactor d)) :=
    (continuousAt_rankOneSparsificationFactor hd).tendsto.comp hratio
  have hseq : ∀ m, ∃ s : I → ℝ,
      (∀ i, 0 ≤ s i) ∧ (Function.support s).ncard ≤ k ∧
      ((1 : Matrix n n ℝ) ≤ ∑ i, s i • Matrix.vecMulVec (v i) (v i)) ∧
      (∑ i, s i • Matrix.vecMulVec (v i) (v i) ≤ beta m • (1 : Matrix n n ℝ)) := by
    intro m
    have hr : 0 < r m := (hbudget m).1
    have : Nonempty (Fin (r m)) := ⟨⟨0, hr⟩⟩
    let V : I × Fin (r m) → n × Fin (r m) → ℝ := frameBlockVector v (r m)
    have hV : ∑ p, Matrix.vecMulVec (V p) (V p) = 1 :=
      sum_vecMulVec_frameBlockVector_eq_one v (r m) hframe
    have hq : Fintype.card (n × Fin (r m)) < q m := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using (hbudget m).2.2.1
    obtain ⟨w, hw, hcard, hlow, hupp⟩ :=
      RankOneBarrier.exists_nonneg_weights_spectral_sandwich_of_card_lt_budget
        (I := I × Fin (r m)) (n := n × Fin (r m)) V hV (q m) hq
    have hcard' : (Function.support w).ncard < r m * (k + 1) :=
      lt_of_le_of_lt hcard (hbudget m).2.2.2
    have hupp' :
        (∑ p, w p • Matrix.vecMulVec (frameBlockVector v (r m) p)
          (frameBlockVector v (r m) p)) ≤
          beta m • (1 : Matrix (n × Fin (r m)) (n × Fin (r m)) ℝ) := by
      simpa only [V, beta, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using hupp
    exact exists_nonneg_weights_spectral_sandwich_of_block_sum v (r m) hr k
      (beta m) w hw hcard' hlow hupp'
  obtain ⟨s, hs, hcard, hlow, hupp⟩ :=
    exists_nonneg_weights_spectral_sandwich_of_tendsto
      v k beta (rankOneSparsificationFactor d) hbeta hseq
  refine ⟨s, hs, ?_, hlow, ?_⟩
  · have hcard' : ((Function.support s).ncard : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hcard
    have hnonneg : 0 ≤ d * (N : ℝ) := by positivity
    exact hcard'.trans (Nat.floor_le hnonneg)
  · exact hupp

end NLAlib
