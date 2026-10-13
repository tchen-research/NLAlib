import NLAlib.Matrix.Inequalities.MajorizationWeights
/-!
# A finite top-cluster weight deficit

Subtracting the boundary gap from the first `k` eigenvalues preserves their
decreasing order. The signed weight-budget maximum principle applied to this
modified list gives the gap-weighted trace deficit needed by the population
Davis–Kahan proof. Source: Yu–Wang–Samworth, Theorem 2.
-/

noncomputable section
namespace NLAlib

/-- A finite prefix indicator sum equals the sum over the prefix
index type. Useful for frame Frobenius and trace budgets. -/
theorem sum_fin_ite_lt_eq_sum_prefix {N k : ℕ} (hk : k ≤ N) (f : Fin N → ℝ) :
    (∑ i : Fin N, if i.val < k then f i else 0)=∑ j : Fin k, f (Fin.castLE hk j) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => Fin.castLE hk j)
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.isLt
  · intro i _ j _ hij
    exact (Fin.castLEEmb hk).injective hij
  · intro i hi
    have hik : i.val < k := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val, hik⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro j _
    rfl

/-- The boundary-gap-shifted decreasing list is still decreasing.
This makes the ordinary finite weight budget yield a quantitative deficit. -/
theorem antitone_sub_prefix_gap {N k : ℕ} (a : Fin N → ℝ) (ha : Antitone a)
    (hk0 : 0 < k) (hkN : k < N) :
    Antitone (fun i => a i-if i.val < k then a ⟨k-1, by omega⟩-a ⟨k, hkN⟩ else 0) := by
  intro i j hij
  by_cases hi : i.val < k <;> by_cases hj : j.val < k
  · simp only [if_pos hi, if_pos hj]
    exact sub_le_sub_right (ha hij) _
  · simp only [if_pos hi, if_neg hj, sub_zero]
    have hi' : i ≤ (⟨k-1, by omega⟩ : Fin N) := by change i.val ≤ k-1; omega
    have hj' : (⟨k, hkN⟩ : Fin N) ≤ j := by change k ≤ j.val; omega
    have ha1 := ha hi'
    have ha2 := ha hj'
    linarith
  · have hij' : i.val ≤ j.val := hij
    omega
  · simp only [if_neg hi, if_neg hj, sub_zero]
    exact ha hij

/-- The loss in a top-`k` linear objective dominates the boundary gap
times missing prefix mass. Yu–Wang–Samworth, Theorem 2, finite trace proof.
Weights are nonnegative contractions of total `k`; no norm conclusion
is assumed. -/
theorem prefix_gap_mul_deficit_le_trace_deficit {N k : ℕ} (a w : Fin N → ℝ)
    (ha : Antitone a) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hk0 : 0 < k) (hkN : k < N) (hbudget : ∑ i, w i=(k : ℝ)) :
    (a ⟨k-1, by omega⟩-a ⟨k, hkN⟩)*
      ((k : ℝ)-∑ j : Fin k, w (Fin.castLE hkN.le j)) ≤
        (∑ j : Fin k, a (Fin.castLE hkN.le j)) - ∑ i, a i*w i := by
  let g := a ⟨k-1, by omega⟩-a ⟨k, hkN⟩
  let b : Fin N → ℝ := fun i => a i-if i.val < k then g else 0
  have hb : Antitone b := antitone_sub_prefix_gap a ha hk0 hkN
  have hmax := sum_mul_le_sum_ite_lt_of_antitone_of_sum_eq b w hb hw0 hw1 hkN.le hbudget
  have heq1 : (∑ i, b i*w i) = (∑ i, a i*w i)-g*∑ i : Fin N, if i.val < k then w i else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [b]
    split_ifs <;> ring
  have heq2 : (∑ i : Fin N, if i.val < k then b i else 0) =
      (∑ i : Fin N, if i.val < k then a i else 0)-g*k := by
    rw [← Finset.sum_filter, ← Finset.sum_filter,
      show (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i.val<k), b i) =
        ∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i.val<k), (a i-g) by
          apply Finset.sum_congr rfl; intro i hi; simp only [b, if_pos (Finset.mem_filter.mp hi).2],
      Finset.sum_sub_distrib, Finset.sum_const, card_filter_fin_lt hkN.le, nsmul_eq_mul]
    ring
  rw [heq1, heq2, sum_fin_ite_lt_eq_sum_prefix hkN.le,
    sum_fin_ite_lt_eq_sum_prefix hkN.le] at hmax
  change g*((k : ℝ)-∑ j : Fin k, w (Fin.castLE hkN.le j)) ≤ _
  nlinarith

end NLAlib
