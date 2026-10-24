import NLAlib.Matrix.Functions.RidgeSpectral
import NLAlib.Matrix.Spectral.EckartYoung

/-!
# Ridge effective dimension and singular-value tails

Splitting the finite ridge spectral sum at a target rank bounds effective dimension by
`k + bestRankFrobSq A k / ρ`. Choosing positive regularization `bestRankFrobSq A k / k`
therefore gives the bound `2k`. The zero-tail case is kept outside that specialization.

Source: Cohen–Musco–Musco 2017, Lemma 4, and
`sketching_lowrank_routes_2026_10_24/sketching.tex`, effective-dimension tail derivation.
Atlas: `ridge-effective-dimension-tail`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Ridge effective dimension is bounded by a target rank plus the squared Frobenius
singular-value tail divided by regularization. This also holds for ranks above a dimension,
where the rank bound directly supplies the conclusion.
atlas: ridge-effective-dimension-tail (partial) -/
theorem ridgeEffectiveDimension_le_rank_add_div_bestRankFrobSq (A : Matrix m n ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ridgeEffectiveDimension A ρ ≤ (k : ℝ) + bestRankFrobSq A k / ρ := by
  have hopt0 : 0 ≤ bestRankFrobSq A k := by
    unfold bestRankFrobSq
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  by_cases hk : k ≤ Fintype.card m
  · let f := fun i : ℕ => singularValues A i ^ 2 / (singularValues A i ^ 2 + ρ)
    have hsplit : ridgeEffectiveDimension A ρ =
        (∑ i ∈ Finset.range k, f i) + ∑ i ∈ Finset.Ico k (Fintype.card m), f i := by
      rw [ridgeEffectiveDimension_eq_sum_singularValues A hρ]
      exact (Finset.sum_range_add_sum_Ico f hk).symm
    have hhead : ∑ i ∈ Finset.range k, f i ≤ (k : ℝ) := by
      calc
        ∑ i ∈ Finset.range k, f i ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact (div_le_one (add_pos_of_nonneg_of_pos (sq_nonneg _) hρ)).2 (by linarith)
        _ = (k : ℝ) := by simp
    have hopt : bestRankFrobSq A k =
        ∑ i ∈ Finset.Ico k (Fintype.card m), singularValues A i ^ 2 := by
      unfold bestRankFrobSq
      rw [← Finset.sum_range_add_sum_Ico _ hk]
      have hz : (∑ i ∈ Finset.range k,
          if k ≤ i then singularValues A i ^ 2 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact if_neg (not_le.mpr (Finset.mem_range.mp hi))
      rw [hz, zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      exact if_pos (Finset.mem_Ico.mp hi).1
    have htail : ∑ i ∈ Finset.Ico k (Fintype.card m), f i ≤ bestRankFrobSq A k / ρ := by
      calc
        ∑ i ∈ Finset.Ico k (Fintype.card m), f i ≤
            ∑ i ∈ Finset.Ico k (Fintype.card m), singularValues A i ^ 2 / ρ := by
          apply Finset.sum_le_sum
          intro i _
          exact div_le_div_of_nonneg_left (sq_nonneg _) hρ
            (le_add_of_nonneg_left (sq_nonneg _))
        _ = bestRankFrobSq A k / ρ := by rw [← Finset.sum_div, hopt]
    rw [hsplit]
    exact add_le_add hhead htail
  · have hr : (A.rank : ℝ) ≤ k := by
      exact_mod_cast A.rank_le_card_height.trans (Nat.le_of_lt (Nat.lt_of_not_ge hk))
    exact (ridgeEffectiveDimension_le_rank A hρ).trans
      (hr.trans (le_add_of_nonneg_right (div_nonneg hopt0 hρ.le)))

/-- A positive squared Frobenius tail divided by a positive target rank is a positive
regularization parameter whose effective dimension is at most twice that rank. No claim
about the inverse-based zero-regularization convention is made when the tail vanishes.
atlas: ridge-effective-dimension-tail (partial) -/
theorem ridgeEffectiveDimension_tail_div_rank_le_two_mul (A : Matrix m n ℝ) {k : ℕ}
    (hk : 1 ≤ k) (htail : 0 < bestRankFrobSq A k) :
    ridgeEffectiveDimension A (bestRankFrobSq A k / k) ≤ 2 * (k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hρ : 0 < bestRankFrobSq A k / k := div_pos htail hk0
  have h := ridgeEffectiveDimension_le_rank_add_div_bestRankFrobSq A hρ k
  have he : bestRankFrobSq A k / (bestRankFrobSq A k / k) = (k : ℝ) := by
    field_simp [ne_of_gt htail, ne_of_gt hk0]
  simpa only [he, two_mul] using h

end NLAlib
