import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concave transfer of finite power deficits

A single positive cutoff compares head deficits with tail mass for any nonnegative
concave function. Zero original tail is handled directly by equality of the ordered
vectors. No division by an individual deficit and no boundary condition `f 0 = 0`
are required.

Source: the scalar cutoff derivation in
`sketching_lowrank_routes_2026_10_24/deterministic_lra.tex`, operator-monotone transfer.
-/

noncomputable section
open scoped BigOperators
open Set

namespace ConcaveOn

/-- A nonnegative concave function lies above every chord from the nonnegative
boundary value, retaining positive values at the origin. -/
theorem div_mul_le_of_nonneg {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f)
    (hf0 : 0 ≤ f 0) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    (b / a) * f a ≤ f b := by
  have ht0 : 0 ≤ b / a := div_nonneg hb ha.le
  have ht1 : b / a ≤ 1 := (div_le_one ha).mpr hba
  have heq : (b / a) • a + (1 - b / a) • (0 : ℝ) = b := by
    simp only [smul_eq_mul, mul_zero, add_zero, div_mul_cancel₀ _ ha.ne']
  have h := hf.2 ha.le (show (0 : ℝ) ∈ Ici 0 by norm_num) ht0
    (sub_nonneg.mpr ht1) (by ring : b / a + (1 - b / a) = 1)
  rw [heq] at h
  change (b / a) * f a + (1 - b / a) * f 0 ≤ f b at h
  have hz := mul_nonneg (sub_nonneg.mpr ht1) hf0
  linarith

/-- Concavity and a nonnegative boundary value make `f(x)/x` antitone on the
positive half-line. -/
theorem div_le_div_of_nonneg {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f)
    (hf0 : 0 ≤ f 0) {t a : ℝ} (ht : 0 < t) (hta : t ≤ a) :
    f a / a ≤ f t / t := by
  have ha : 0 < a := ht.trans_le hta
  apply (div_le_div_iff₀ ha ht).mpr
  calc
    f a * t = a * ((t / a) * f a) := by field_simp [ha.ne']
    _ ≤ a * f t := mul_le_mul_of_nonneg_left
      (hf.div_mul_le_of_nonneg hf0 ha ht.le hta) ha.le
    _ = f t * a := mul_comm _ _

/-- Every nonnegative power of a concave chord gives the lower cutoff comparison.
The smaller argument may be zero and the function may be positive at zero. -/
theorem div_rpow_mul_rpow_le {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f)
    (hfn : ∀ x, 0 ≤ x → 0 ≤ f x) {a b p : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hba : b ≤ a) (hp : 0 ≤ p) : (f a / a) ^ p * b ^ p ≤ f b ^ p := by
  have h := Real.rpow_le_rpow (mul_nonneg (div_nonneg hb ha.le) (hfn a ha.le))
    (hf.div_mul_le_of_nonneg (hfn 0 le_rfl) ha hb hba) hp
  rw [Real.mul_rpow (div_nonneg hb ha.le) (hfn a ha.le), Real.div_rpow hb ha.le] at h
  rw [Real.div_rpow (hfn a ha.le) ha.le]
  convert h using 1
  ring

/-- The head power deficit is controlled by the ratio at its larger argument. -/
theorem rpow_sub_rpow_le_div_rpow_mul {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Ici 0) f) (hfn : ∀ x, 0 ≤ x → 0 ≤ f x)
    {a b p : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) (hp : 0 ≤ p) :
    f a ^ p - f b ^ p ≤ (f a / a) ^ p * (a ^ p - b ^ p) := by
  have hlow := hf.div_rpow_mul_rpow_le hfn ha hb hba hp
  have heq : (f a / a) ^ p * a ^ p = f a ^ p := by
    rw [Real.div_rpow (hfn a ha.le) ha.le,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos ha p).ne']
  rw [mul_sub, heq]
  linarith

/-- A sorted nonnegative vector's relative power-deficit certificate transfers
through every nonnegative concave function, at every positive real power. The cutoff
may be zero, the prefix may be empty, and `f 0` may be positive. -/
theorem sum_rpow_sub_prefix_le {N k : ℕ} (a b : Fin N → ℝ)
    (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (hba : ∀ i, b i ≤ a i) (hk : k < N) {p ε : ℝ} (hp : 0 < p) (hε : 0 ≤ ε)
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f) (hfn : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hdeficit : (∑ i, a i ^ p) - (∑ i, if i.val < k then b i ^ p else 0) ≤
      (1 + ε) * (∑ i, if k ≤ i.val then a i ^ p else 0)) :
    (∑ i, f (a i) ^ p) - (∑ i, if i.val < k then f (b i) ^ p else 0) ≤
      (1 + ε) * (∑ i, if k ≤ i.val then f (a i) ^ p else 0) := by
  classical
  have hsplit (g : Fin N → ℝ) : (∑ i, g i) =
      (∑ i, if i.val < k then g i else 0) + (∑ i, if k ≤ i.val then g i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < k
    · simp only [if_pos hi, if_neg (not_le.mpr hi), add_zero]
    · simp only [if_neg hi, if_pos (not_lt.mp hi), zero_add]
  have hheadSub (g h : Fin N → ℝ) :
      (∑ i, if i.val < k then g i - h i else 0) =
        (∑ i, if i.val < k then g i else 0) - (∑ i, if i.val < k then h i else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  let t := a ⟨k, hk⟩
  by_cases ht : 0 < t
  · let c := (f t / t) ^ p
    have hc : 0 ≤ c := Real.rpow_nonneg (div_nonneg (hfn t ht.le) ht.le) _
    have hbudget : (∑ i, if i.val < k then a i ^ p - b i ^ p else 0) ≤
        ε * (∑ i, if k ≤ i.val then a i ^ p else 0) := by
      rw [hheadSub]
      rw [hsplit (fun i => a i ^ p)] at hdeficit
      nlinarith
    have hhead : (∑ i, if i.val < k then f (a i) ^ p - f (b i) ^ p else 0) ≤
        c * (∑ i, if i.val < k then a i ^ p - b i ^ p else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i.val < k
      · rw [if_pos hi, if_pos hi]
        have hta : t ≤ a i := ha (show i ≤ (⟨k, hk⟩ : Fin N) from hi.le)
        have hai : 0 < a i := ht.trans_le hta
        have hr : (f (a i) / a i) ^ p ≤ c := Real.rpow_le_rpow
          (div_nonneg (hfn _ (ha0 i)) hai.le)
          (hf.div_le_div_of_nonneg (hfn 0 le_rfl) ht hta) hp.le
        exact (hf.rpow_sub_rpow_le_div_rpow_mul hfn hai (hb0 i) (hba i) hp.le).trans
          (mul_le_mul_of_nonneg_right hr
            (sub_nonneg.mpr (Real.rpow_le_rpow (hb0 i) (hba i) hp.le)))
      · simp only [if_neg hi, mul_zero, le_refl]
    have htail : c * (∑ i, if k ≤ i.val then a i ^ p else 0) ≤
        ∑ i, if k ≤ i.val then f (a i) ^ p else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : k ≤ i.val
      · rw [if_pos hi, if_pos hi]
        exact hf.div_rpow_mul_rpow_le hfn ht (ha0 i)
          (ha (show (⟨k, hk⟩ : Fin N) ≤ i from hi)) hp.le
      · simp only [if_neg hi, mul_zero, le_refl]
    have hcombined := hhead.trans (mul_le_mul_of_nonneg_left hbudget hc)
    have hlast := mul_le_mul_of_nonneg_left htail hε
    rw [hheadSub] at hcombined
    rw [hsplit (fun i => f (a i) ^ p)]
    nlinarith
  · have ht0 : t = 0 := le_antisymm (not_lt.mp ht) (ha0 _)
    have htail0 : (∑ i, if k ≤ i.val then a i ^ p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : k ≤ i.val
      · have hai : a i = 0 := le_antisymm
          ((ha (show (⟨k, hk⟩ : Fin N) ≤ i from hi)).trans ht0.le) (ha0 i)
        simp only [if_pos hi, hai, Real.zero_rpow hp.ne']
      · simp only [if_neg hi]
    rw [htail0, mul_zero] at hdeficit
    have hsumB : (∑ i, if i.val < k then b i ^ p else 0) ≤ ∑ i, b i ^ p := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (hb0 i) _
    have hnn (i : Fin N) : 0 ≤ a i ^ p - b i ^ p :=
      sub_nonneg.mpr (Real.rpow_le_rpow (hb0 i) (hba i) hp.le)
    have hsum0 : (∑ i, (a i ^ p - b i ^ p)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have hnonneg := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        Real.rpow_le_rpow (hb0 i) (hba i) hp.le)
      linarith
    have hab (i : Fin N) : a i = b i := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hsum0 i (Finset.mem_univ i)
      apply le_antisymm _ (hba i)
      exact (Real.rpow_le_rpow_iff (ha0 i) (hb0 i) hp).mp (sub_eq_zero.mp hi).le
    simp_rw [← hab]
    rw [hsplit (fun i => f (a i) ^ p)]
    have hnonneg : 0 ≤ ∑ i, if k ≤ i.val then f (a i) ^ p else 0 :=
      Finset.sum_nonneg fun i _ => by split_ifs; exacts [Real.rpow_nonneg (hfn _ (ha0 i)) _, le_rfl]
    nlinarith

end ConcaveOn
