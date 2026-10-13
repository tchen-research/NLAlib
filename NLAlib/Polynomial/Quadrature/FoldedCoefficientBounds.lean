import NLAlib.Polynomial.Quadrature.FoldedMomentBounds
import NLAlib.ForMathlib.Analysis.InversePowerSeries

/-! # Weighted finite alias blocks

Summing the finite period mass against an inverse-power coefficient envelope
gives the stronger eventual Clenshaw–Curtis rate.
-/
noncomputable section
open Finset
namespace NLAlib

/-- Folding an even frequency depends only on its index modulo the grid size.
Source: the finite-block proof in the focused quadrature reroute. -/
theorem chebyshevAliasIndex_two_mul_add_mul {n : ℕ} (_hn : 0 < n) (l r : ℕ) :
    chebyshevAliasIndex n (2 * (l * n + r)) = chebyshevAliasIndex n (2 * r) := by
  unfold chebyshevAliasIndex
  have hmod : 2 * (l * n + r) % (2 * n) = 2 * r % (2 * n) := by
    rw [show 2 * (l * n + r) = 2 * r + l * (2 * n) by ring,
      Nat.add_mul_mod_self_right]
  rw [hmod]

/-- The positive even Lebesgue moments have total absolute mass at most one.
Source: the finite telescope in the focused quadrature reroute. -/
theorem tsum_abs_chebyshevMoment_two_mul_succ_le_one :
    (∑' j : ℕ, |chebyshevMoment (2 * (j + 1))|) ≤ 1 := by
  apply Real.tsum_le_of_sum_range_le (fun j => abs_nonneg _)
  intro m
  rw [sum_abs_chebyshevMoment_two_mul_succ]
  exact sub_le_self _ (by positivity)

/-- The positive even moment sequence is absolutely summable.
Source: the finite telescope in the focused quadrature reroute. -/
theorem summable_abs_chebyshevMoment_two_mul_succ :
    Summable (fun j : ℕ => |chebyshevMoment (2 * (j + 1))|) := by
  apply summable_of_sum_range_le (c := 1) (fun j => abs_nonneg _)
  intro m
  rw [sum_abs_chebyshevMoment_two_mul_succ]
  exact sub_le_self _ (by positivity)

/-- The unfurled even tail under an inverse-power coefficient envelope is at most
`A/n^p`. Source: focused quadrature reroute; the positive even moment mass is one. -/
theorem tsum_abs_mul_chebyshevMoment_even_tail_le
    {c : ℕ → ℝ} (hcS : Summable (fun k => |c k|)) {n p : ℕ}
    (hn : 0 < n) {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ k, n < k → |c k| ≤ A / (k : ℝ) ^ p) :
    (∑' j : ℕ, if n < 2 * j then |c (2 * j)| * |chebyshevMoment (2 * j)| else 0) ≤
      A / (n : ℝ) ^ p := by
  let t := fun j : ℕ => if n < 2 * j then |c (2 * j)| * |chebyshevMoment (2 * j)| else 0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc2S : Summable (fun j => |c (2 * j)|) := by
    exact hcS.comp_injective (show Function.Injective (fun j : ℕ => 2 * j) by intro a b h; dsimp only at h; omega)
  have ht : Summable t := by
    refine Summable.of_nonneg_of_le (fun j => by dsimp [t]; split_ifs <;> positivity) ?_ (hc2S.mul_left 2)
    intro j
    dsimp [t]
    split_ifs
    · have h := mul_le_mul_of_nonneg_left (abs_chebyshevMoment_le_two (2 * j)) (abs_nonneg (c (2 * j)))
      simpa only [mul_comm] using h
    · positivity
  have hb (j : ℕ) : t (j + 1) ≤ A / (n : ℝ) ^ p * |chebyshevMoment (2 * (j + 1))| := by
    dsimp [t]
    split_ifs with hk
    · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      refine (hc _ hk).trans ?_
      apply div_le_div_of_nonneg_left hA (by positivity)
      apply pow_le_pow_left₀ hnR.le
      exact_mod_cast hk.le
    · positivity
  have h := (ht.comp_injective Nat.succ_injective).tsum_le_tsum hb
    (summable_abs_chebyshevMoment_two_mul_succ.mul_left (A / (n : ℝ) ^ p))
  rw [tsum_mul_left] at h
  have hmass := mul_le_mul_of_nonneg_left tsum_abs_chebyshevMoment_two_mul_succ_le_one
    (show 0 ≤ A / (n : ℝ) ^ p by positivity)
  change (∑' j, t j) ≤ _
  rw [ht.tsum_eq_zero_add, show t 0 = 0 by simp [t], zero_add]
  exact h.trans (by simpa only [mul_one] using hmass)

/-- The folded even tail under an inverse-power coefficient envelope is at most
`6A/n^p`, for `p≥2`. Source: focused quadrature reroute, finite alias-block estimate. -/
theorem tsum_abs_mul_chebyshevMoment_alias_even_tail_le
    {c : ℕ → ℝ} (hcS : Summable (fun k => |c k|)) {n p : ℕ}
    (hn : 2 ≤ n) (hp : 2 ≤ p) {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ k, n < k → |c k| ≤ A / (k : ℝ) ^ p) :
    (∑' j : ℕ, if n < 2 * j then
      |c (2 * j)| * |chebyshevMoment (chebyshevAliasIndex n (2 * j))| else 0) ≤
        6 * A / (n : ℝ) ^ p := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let t := fun j : ℕ => if n < 2 * j then
    |c (2 * j)| * |chebyshevMoment (chebyshevAliasIndex n (2 * j))| else 0
  have ht0 (j : ℕ) : 0 ≤ t j := by dsimp [t]; split_ifs <;> positivity
  have hc2S : Summable (fun j => |c (2 * j)|) := by
    exact hcS.comp_injective (show Function.Injective (fun j : ℕ => 2 * j) by intro a b h; dsimp only at h; omega)
  have ht : Summable t := by
    refine Summable.of_nonneg_of_le ht0 ?_ (hc2S.mul_left 2)
    intro j
    dsimp [t]
    split_ifs
    · have h := mul_le_mul_of_nonneg_left
        (abs_chebyshevMoment_le_two (chebyshevAliasIndex n (2 * j))) (abs_nonneg (c (2 * j)))
      simpa only [mul_comm] using h
    · positivity
  let B := fun l : ℕ => ∑ r : Fin n, t (l * n + r)
  have : NeZero n := ⟨by omega⟩
  have htP : Summable (fun z : ℕ × Fin n => t (z.1 * n + z.2)) := by
    simpa only [Function.comp_def, Nat.divModEquiv_symm_apply] using ht.comp_injective (Nat.divModEquiv n).symm.injective
  have hB : Summable B := by
    simpa only [B, tsum_fintype] using htP.prod
  have htot : (∑' j, t j) = ∑' l, B l := by
    have he := (Nat.divModEquiv n).symm.tsum_eq t
    simp only [Nat.divModEquiv_symm_apply] at he
    rw [← he, htP.tsum_prod]
    simp only [B, tsum_fintype]
  have hmass : (∑ r : Fin n, |chebyshevMoment (chebyshevAliasIndex n (2 * r))|) ≤ 4 := by
    rw [sum_fin_eq_sum_range]
    convert sum_abs_chebyshevMoment_alias_two_mul_le_four hn0 using 1
    apply sum_congr rfl
    intro r hr
    rw [dif_pos (mem_range.mp hr)]
  have hblock (l : ℕ) (D : ℝ) (hD : 0 ≤ D)
      (hDk : ∀ r : Fin n, n < 2 * (l * n + r) → |c (2 * (l * n + r))| ≤ D) :
      B l ≤ 4 * D := by
    calc
      B l ≤ ∑ r : Fin n, D * |chebyshevMoment (chebyshevAliasIndex n (2 * r))| := by
        apply sum_le_sum
        intro r hr
        dsimp [t]
        split_ifs with hk
        · rw [chebyshevAliasIndex_two_mul_add_mul hn0]
          exact mul_le_mul_of_nonneg_right (hDk r hk) (abs_nonneg _)
        · positivity
      _ = D * ∑ r : Fin n, |chebyshevMoment (chebyshevAliasIndex n (2 * r))| := by rw [mul_sum]
      _ ≤ D * 4 := mul_le_mul_of_nonneg_left hmass hD
      _ = 4 * D := mul_comm _ _
  have hB0 : B 0 ≤ 4 * A / (n : ℝ) ^ p := by
    have h := hblock 0 (A / (n : ℝ) ^ p) (by positivity) (by
      intro r hr
      refine (hc _ hr).trans ?_
      apply div_le_div_of_nonneg_left hA (by positivity)
      apply pow_le_pow_left₀ hnR.le
      exact_mod_cast hr.le)
    simpa only [mul_div_assoc] using h
  have hBs (l : ℕ) : B (l + 1) ≤
      (4 * A / (2 * (n : ℝ)) ^ p) * (((l + 1 : ℕ) : ℝ) ^ p)⁻¹ := by
    have hlR : (0 : ℝ) < (l + 1 : ℕ) := by positivity
    have h := hblock (l + 1) (A / (2 * ((l + 1 : ℕ) : ℝ) * n) ^ p) (by positivity) (by
      intro r hr
      refine (hc _ hr).trans ?_
      apply div_le_div_of_nonneg_left hA (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show 2 * (l + 1) * n ≤ 2 * ((l + 1) * n + (r : ℕ)) by rw [Nat.mul_assoc]; omega))
    refine h.trans_eq ?_
    rw [show 2 * ((l + 1 : ℕ) : ℝ) * n = 2 * n * ((l + 1 : ℕ) : ℝ) by ring, mul_pow]
    ring
  have hg : Summable (fun l : ℕ => (((l + 1 : ℕ) : ℝ) ^ p)⁻¹) := by
    simpa only [Function.comp_def] using (Real.summable_nat_pow_inv.mpr (show 1 < p by omega)).comp_injective Nat.succ_injective
  have htail := (hB.comp_injective Nat.succ_injective).tsum_le_tsum hBs (hg.mul_left _)
  rw [tsum_mul_left] at htail
  have hg2 := tsum_inv_pow_nat_succ_le_two hp
  have htail2 : (∑' l, B (l + 1)) ≤ 8 * A / (2 * (n : ℝ)) ^ p := by
    have hmul := mul_le_mul_of_nonneg_left hg2 (show 0 ≤ 4 * A / (2 * (n : ℝ)) ^ p by positivity)
    refine htail.trans (hmul.trans_eq ?_)
    ring
  have hpow : (4 : ℝ) ≤ 2 ^ p := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
    norm_num at h
    exact h
  have htail3 : 8 * A / (2 * (n : ℝ)) ^ p ≤ 2 * A / (n : ℝ) ^ p := by
    rw [mul_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ 2 * A * (n : ℝ) ^ p by positivity)
    nlinarith
  change (∑' j, t j) ≤ _
  rw [htot, hB.tsum_eq_zero_add]
  have h := add_le_add hB0 (htail2.trans htail3)
  exact h.trans_eq (by ring)

end NLAlib
