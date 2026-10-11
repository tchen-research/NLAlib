import NLAlib.Matrix.MajorizationProperties

/-!
# Finite threshold certificates for Schur–Horn

A weight allocation with no strictly inverted occupied/vacant pair minimizes
every equal-cardinality subset sum. This signed scalar certificate is step (7)
of the supplied variational rederivation of Horn–Johnson (2013), Theorem 4.3.45.
It supports the atlas result `schur-horn` without a spectral sorting of blocks.
-/

noncomputable section
open scoped BigOperators

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A scalar threshold separates occupied and vacant weights whenever every
occupied/vacant pair is weakly ordered. Schur–Horn variational rederivation,
step (7), for arbitrary signed values and repeated values. -/
theorem exists_threshold_of_weight_order (a p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (horder : ∀ i j, 0 < p i → p j < 1 → a i ≤ a j)
    (hpos : ∃ i, 0 < p i) :
    ∃ γ : ℝ, (∀ i, (a i - γ) * p i ≤ 0) ∧
      ∀ i, 0 ≤ (a i - γ) * (1 - p i) := by
  classical
  let S : Finset ι := Finset.univ.filter fun i => 0 < p i
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, by simp [S, hi]⟩
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image a hS
  have hjp : 0 < p j := (Finset.mem_filter.mp hj).2
  refine ⟨a j, ?_, ?_⟩
  · intro i
    by_cases hi : 0 < p i
    · exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hmax i (by simp [S, hi]))) (hp0 i)
    · have hi0 : p i = 0 := le_antisymm (le_of_not_gt hi) (hp0 i)
      simp [hi0]
  · intro i
    by_cases hi : p i < 1
    · exact mul_nonneg (sub_nonneg.mpr (horder j i hjp hi))
        (sub_nonneg.mpr (hp1 i))
    · have hi1 : p i = 1 := le_antisymm (hp1 i) (le_of_not_gt hi)
      simp [hi1]

/-- A weight allocation of integer mass with weakly ordered occupied/vacant
pairs has weighted value at most every subset sum of that cardinality.
Schur–Horn variational rederivation, step (7); empty allocations are included. -/
theorem sum_mul_le_sum_of_weight_order (a p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (horder : ∀ i j, 0 < p i → p j < 1 → a i ≤ a j)
    (T : Finset ι) (hbudget : ∑ i, p i = (T.card : ℝ)) :
    (∑ i, a i * p i) ≤ ∑ i ∈ T, a i := by
  classical
  by_cases hpos : ∃ i, 0 < p i
  · obtain ⟨γ, hleft, hright⟩ :=
      exists_threshold_of_weight_order a p hp0 hp1 horder hpos
    have hnonneg : 0 ≤ (∑ i ∈ T, (a i - γ) * (1 - p i)) -
        ∑ i ∈ Tᶜ, (a i - γ) * p i := by
      exact sub_nonneg.mpr ((Finset.sum_nonpos fun i _ => hleft i).trans
        (Finset.sum_nonneg fun i _ => hright i))
    have htotal : (∑ i, (a i - γ) * p i) =
        (∑ i, a i * p i) - γ * T.card := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hbudget]
    have hsplit := T.sum_add_sum_compl (fun i => (a i - γ) * p i)
    have hT : (∑ i ∈ T, (a i - γ) * (1 - p i)) =
        (∑ i ∈ T, a i) - γ * T.card - ∑ i ∈ T, (a i - γ) * p i := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const]
      simp [nsmul_eq_mul, mul_comm]
    rw [hT] at hnonneg
    linarith
  · have hp : ∀ i, p i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt fun hi => hpos ⟨i, hi⟩) (hp0 i)
    have hcard : T.card = 0 := by simpa [hp] using hbudget.symm
    have hT : T = ∅ := Finset.card_eq_zero.mp hcard
    simp [hp, hT]

/-- An integer-mass allocation whose occupied/vacant pairs are weakly ordered
is bounded above by the attained bottom-coordinate sum. Schur–Horn variational
rederivation, step (7), with arbitrary signs and both empty/full endpoints. -/
theorem sum_mul_le_sum_sub_sumLargest_of_weight_order (a p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (horder : ∀ i j, 0 < p i → p j < 1 → a i ≤ a j)
    {k : ℕ} (hk : k ≤ Fintype.card ι) (hbudget : ∑ i, p i = (k : ℝ)) :
    (∑ i, a i * p i) ≤ (∑ i, a i) - sumLargest a (Fintype.card ι - k) := by
  let U := largestCoordinates a (Fintype.card ι - k)
  have hcardU : U.card = Fintype.card ι - k :=
    card_largestCoordinates a (Nat.sub_le _ _)
  have hcardT : Uᶜ.card = k := by rw [Finset.card_compl, hcardU]; omega
  have hsumU : (∑ i ∈ U, a i) = sumLargest a (Fintype.card ι - k) :=
    sum_largestCoordinates a _
  have hsplit := U.sum_add_sum_compl a
  have hbound := sum_mul_le_sum_of_weight_order a p hp0 hp1 horder Uᶜ
    (by rw [hcardT]; exact hbudget)
  rw [hsumU] at hsplit
  linarith

end NLAlib
