import NLAlib.Matrix.Structured.ProfileMasks
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Entry bounds for the three profile masks

The residual mask converts the heavy-neighbor inequalities into rapid row
decay. In particular its logarithmically weighted entry envelope is bounded by
the original maximum row energy. This is the deterministic part of the
remainder estimate in Latała--van Handel--Youssef (2018), Section 3.2.
-/

noncomputable section

namespace NLAlib

/-- A residual entry in the interval between two neighbor cutoffs either
crosses an early main cutoff or crosses one of the next two neighbor cutoffs. -/
theorem remainder_entry_cases {i j k : ℕ} (hij : ProfileRemainderMask i j)
    (hi : profileNeighborCutoff k ≤ i) (hi' : i < profileNeighborCutoff (k + 1)) :
    j < profileCutoff k ∨
      (i < profileCutoff (k + 1) ∧ profileNeighborCutoff (k + 1) ≤ j) ∨
      (i < profileCutoff (k + 2) ∧ profileNeighborCutoff (k + 2) ≤ j) := by
  have hblock : InProfileBlock (k + 1) i :=
    ⟨(profileCutoff_le_neighborCutoff k).trans hi, hi'⟩
  have hnot := not_inProfileBlock_pair_of_remainder hij hblock
  by_cases hj : j < profileCutoff k
  · exact Or.inl hj
  have hj' : profileNeighborCutoff (k + 1) ≤ j := by
    change ¬ (profileCutoff k ≤ j ∧ j < profileNeighborCutoff (k + 1)) at hnot
    omega
  by_cases hin : i < profileCutoff (k + 1)
  · exact Or.inr (Or.inl ⟨hin, hj'⟩)
  have hi'' : i < profileCutoff (k + 2) :=
    hi'.trans (profileNeighborCutoff_lt_cutoff_succ (k + 1))
  have hblock' : InProfileBlock (k + 2) i :=
    ⟨Nat.le_of_not_gt hin, hi'.trans_le
      (monotone_profileNeighborCutoff (by omega : k + 1 ≤ k + 2))⟩
  have hnot' := not_inProfileBlock_pair_of_remainder hij hblock'
  change ¬ (profileCutoff (k + 1) ≤ j ∧ j < profileNeighborCutoff (k + 2)) at hnot'
  exact Or.inr (Or.inr ⟨hi'', by
    have hlow := (profileCutoff_le_neighborCutoff (k + 1)).trans hj'
    omega⟩)

/-- The residual mask has the source's inverse-square-root neighbor decay on
each interval between consecutive neighbor cutoffs. -/
theorem profileRemainderPart_le_div_sqrt_previous
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) {a : ℝ} (ha : 0 ≤ a)
    (hcross : ∀ k i j, profileNeighborCutoff k ≤ i.val → j.val < profileCutoff k →
      A i j ≤ a / Real.sqrt (profilePreviousCutoff k))
    (k : ℕ) (i j : Fin n) (hi : profileNeighborCutoff k ≤ i.val)
    (hi' : i.val < profileNeighborCutoff (k + 1)) :
    profileRemainderPart A i j ≤ a / Real.sqrt (profilePreviousCutoff k) := by
  classical
  unfold profileRemainderPart
  split_ifs with hij
  · rcases remainder_entry_cases hij hi hi' with hj | ⟨hi'', hj⟩ | ⟨hi'', hj⟩
    · exact hcross k i j hi hj
    · have h := hcross (k + 1) j i hj hi''
      have hsym : A j i = A i j := congrFun (congrFun hA i) j
      rw [hsym] at h
      apply h.trans
      apply div_le_div_of_nonneg_left ha (sqrt_profilePreviousCutoff_pos k)
      apply Real.sqrt_le_sqrt
      exact_mod_cast monotone_profilePreviousCutoff (by omega : k ≤ k + 1)
    · have h := hcross (k + 2) j i hj hi''
      have hsym : A j i = A i j := congrFun (congrFun hA i) j
      rw [hsym] at h
      apply h.trans
      apply div_le_div_of_nonneg_left ha (sqrt_profilePreviousCutoff_pos k)
      apply Real.sqrt_le_sqrt
      exact_mod_cast monotone_profilePreviousCutoff (by omega : k ≤ k + 2)
  · exact div_nonneg ha (Real.sqrt_nonneg _)

/-- A nonempty diagonal block beyond the initial block inherits the row
threshold at the preceding main cutoff. -/
theorem entry_le_div_sqrt_log_of_inProfileBlock
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {b : ℝ}
    (hrow : ∀ k i j, profileCutoff k ≤ i.val →
      A i j ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k)))
    (k : ℕ) (i j : Fin n) (hi : InProfileBlock (k + 1) i.val) :
    A i j ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k)) :=
  hrow k i j hi.1

/-- The square-root neighbor scale dominates an ordinary exponential. -/
theorem two_pow_le_sqrt_profilePreviousCutoff (k : ℕ) :
    (2 : ℝ) ^ k ≤ Real.sqrt (profilePreviousCutoff k : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  have h : (2 : ℕ) ^ (2 * k) ≤ 2 ^ (2 ^ k) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_pow (by decide : 2 ≠ 1) k)
  have h' : (2 : ℝ) ^ (2 * k) ≤ (profilePreviousCutoff k : ℝ) := by
    exact_mod_cast h
  simpa [pow_mul, mul_comm] using h'

/-- Up to the next neighbor cutoff, the logarithmic position weight is at
most eight times the square root of the present previous cutoff. -/
theorem log_le_eight_mul_sqrt_previous {i k : ℕ}
    (hi : i < profileNeighborCutoff (k + 1)) :
    Real.log (i + 1 : ℝ) ≤ 8 * Real.sqrt (profilePreviousCutoff k : ℝ) := by
  have hi' : i + 1 ≤ profileCutoff (k + 2) :=
    (Nat.succ_le_of_lt hi).trans
      (profileNeighborCutoff_lt_cutoff_succ (k + 1)).le
  have hlog : Real.log (i + 1 : ℝ) ≤ Real.log (profileCutoff (k + 2) : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hi'
  rw [log_profileCutoff] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpow : (2 : ℝ) ^ (k + 2 + 1) = 8 * 2 ^ k := by
    rw [show k + 2 + 1 = k + 3 by omega, pow_add]
    norm_num
    ring
  rw [hpow] at hlog
  exact hlog.trans ((mul_le_mul_of_nonneg_left htwo (by positivity)).trans
    (by nlinarith [two_pow_le_sqrt_profilePreviousCutoff k]))

private theorem exists_neighbor_interval {i : ℕ} (hi : profileNeighborCutoff 0 ≤ i) :
    ∃ k, profileNeighborCutoff k ≤ i ∧ i < profileNeighborCutoff (k + 1) := by
  have hex : ∃ t, i < profileNeighborCutoff t :=
    ⟨i + 1, (Nat.lt_succ_self i).trans_le
      ((le_profileCutoff (i + 1)).trans (profileCutoff_le_neighborCutoff (i + 1)))⟩
  have ht := Nat.find_spec hex
  have ht0 : Nat.find hex ≠ 0 := by intro h; rw [h] at ht; omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  refine ⟨k, ?_, ?_⟩
  · have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    omega
  · simpa [hk] using ht

/-- The residual mask has a dimension-free logarithmic entry envelope bounded
by eight times the original row-energy bound. This is the deterministic
input to the weak Gaussian-process estimate for the residual matrix. -/
theorem profileRemainderPart_mul_log_le_eight_mul
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) {a : ℝ} (ha : 0 ≤ a)
    (hA0 : ∀ i j, 0 ≤ A i j) (hentry : ∀ i j, A i j ≤ a)
    (hcross : ∀ k i j, profileNeighborCutoff k ≤ i.val → j.val < profileCutoff k →
      A i j ≤ a / Real.sqrt (profilePreviousCutoff k)) (i j : Fin n) :
    profileRemainderPart A i j * Real.log (i.val + 1) ≤ 8 * a := by
  classical
  have hnonneg : 0 ≤ profileRemainderPart A i j := by
    unfold profileRemainderPart
    split_ifs
    · exact hA0 i j
    · exact le_rfl
  by_cases hi : profileNeighborCutoff 0 ≤ i.val
  · obtain ⟨k, hk, hk'⟩ := exists_neighbor_interval hi
    have hdecay := (le_div_iff₀ (sqrt_profilePreviousCutoff_pos k)).mp
      (profileRemainderPart_le_div_sqrt_previous A hA ha hcross k i j hk hk')
    have hlog := log_le_eight_mul_sqrt_previous hk'
    nlinarith [mul_le_mul_of_nonneg_left hlog hnonneg]
  · have hrem : profileRemainderPart A i j ≤ a := by
      unfold profileRemainderPart
      split_ifs
      · exact hentry i j
      · exact ha
    have hlog' : Real.log (i.val + 1 : ℝ) ≤ 4 := by
      have hi' : i.val + 1 ≤ profileCutoff 1 :=
        (Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)).trans
          (profileNeighborCutoff_lt_cutoff_succ 0).le
      have h := Real.log_le_log (by positivity : (0 : ℝ) < i.val + 1)
        (show (i.val + 1 : ℝ) ≤ profileCutoff 1 by exact_mod_cast hi')
      rw [log_profileCutoff] at h
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h hl
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hlog' hnonneg]

end NLAlib
