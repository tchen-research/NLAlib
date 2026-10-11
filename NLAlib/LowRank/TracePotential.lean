import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import NLAlib.LowRank.TraceDrift

/-!
# Scalar potential for relative trace convergence

The potential `1/a - log a` advances by at least `1/r` under the normalized
RPCholesky trace recursion. This is the scalar estimate of manuscript `sa:rp-theorem`.
-/

noncomputable section
namespace NLAlib

/-- The scalar trace potential advances by one reciprocal-rank unit under a Cholesky
trace-recursion step. Source: manuscript `sa:rp-theorem`; CETW (2025), scalar completion.
The supporting-line inequality is proved by scalar reciprocal algebra and `log x ≤ x-1`. -/
theorem one_div_le_inv_sub_log_sub_of_step_le
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hstep : b ≤ a - a ^ 2 / (r * (a + 1))) :
    1 / r ≤ (b⁻¹ - Real.log b) - (a⁻¹ - Real.log a) := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hlog
  have hinv : 0 ≤ b⁻¹ - a⁻¹ - (a - b) / a ^ 2 := by
    have he : b⁻¹ - a⁻¹ - (a - b) / a ^ 2 = (a - b) ^ 2 / (a ^ 2 * b) := by
      field_simp
    rw [he]
    positivity
  have hdelta : a ^ 2 / (r * (a + 1)) ≤ a - b := by linarith
  have hgain := mul_le_mul_of_nonneg_right hdelta
    (by positivity : 0 ≤ (a + 1) / a ^ 2)
  have he : a ^ 2 / (r * (a + 1)) * ((a + 1) / a ^ 2) = 1 / r := by
    field_simp
  rw [he] at hgain
  have he' : (a - b) * ((a + 1) / a ^ 2) = (a - b) / a ^ 2 + (1 - b / a) := by
    field_simp
    ring
  rw [he'] at hgain
  linarith

/-- The scalar trace potential is strictly decreasing on the positive half-line.
Source: manuscript `sa:rp-theorem`, potential comparison. -/
theorem inv_sub_log_lt_inv_sub_log {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    b⁻¹ - Real.log b < a⁻¹ - Real.log a := by
  have hb : 0 < b := ha.trans hab
  have hi : b⁻¹ < a⁻¹ := (inv_lt_inv₀ hb ha).2 hab
  have hl : Real.log a < Real.log b := Real.log_lt_log ha hab
  linarith

/-- The normalized relative-trace recursion gives the exact logarithmic pivot budget.
Source: manuscript `sa:rp-theorem`; CETW (2025), scalar completion. This reusable
scalar theorem includes all positive tolerances and negative budget expressions.
The adaptive matrix process supplies its recursion separately. -/
theorem le_mul_tail_of_traceExcessDrift_recursion
    (u : ℕ → ℝ) (hmono : Antitone u) {τ r ε : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    (hε : 0 < ε) (hrec : ∀ t, u (t + 1) ≤ u t - traceExcessDrift τ (u t) / r)
    (k : ℕ) (hbudget : r / ε + r * Real.log (u 0 / (ε * τ)) ≤ k) :
    u k ≤ (1 + ε) * τ := by
  by_contra hfail
  have huk : (1 + ε) * τ < u k := lt_of_not_ge hfail
  let a := fun t => u t / τ - 1
  have hapos : ∀ t, t ≤ k → ε < a t := by
    intro t ht
    change ε < u t / τ - 1
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hτ]
    have h := hmono ht
    nlinarith
  have hstep : ∀ t, t < k → a (t + 1) ≤ a t - (a t) ^ 2 / (r * (a t + 1)) := by
    intro t ht
    have hap : 0 < a t := hε.trans (hapos t ht.le)
    have hut : τ < u t := by
      have h := hapos t ht.le
      dsimp only [a] at h
      rw [lt_sub_iff_add_lt, lt_div_iff₀ hτ] at h
      nlinarith
    have hua : u t = (a t + 1) * τ := by
      dsimp only [a]
      field_simp
      ring
    have hdelta : (traceExcessDrift τ (u t) / r) / τ =
        (a t) ^ 2 / (r * (a t + 1)) := by
      rw [traceExcessDrift, max_eq_left (sub_nonneg.mpr hut.le), hua]
      field_simp
      ring
    have h := div_le_div_of_nonneg_right (hrec t) hτ.le
    rw [sub_div, hdelta] at h
    change u (t + 1) / τ ≤ u t / τ - (a t) ^ 2 / (r * (a t + 1)) at h
    dsimp only [a]
    linarith
  let φ := fun t => (a t)⁻¹ - Real.log (a t)
  have hsum : (k : ℝ) / r ≤ φ k - φ 0 := by
    have h := Finset.sum_le_sum (s := Finset.range k) (f := fun _ => (1 : ℝ) / r)
      (g := fun t => φ (t + 1) - φ t) (fun t ht =>
        one_div_le_inv_sub_log_sub_of_step_le
          (hε.trans (hapos t (Finset.mem_range.mp ht).le))
          (hε.trans (hapos (t + 1) (by have := Finset.mem_range.mp ht; omega))) hr
          (hstep t (Finset.mem_range.mp ht)))
    rw [Finset.sum_range_sub] at h
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div] using h
  have hφk : φ k < ε⁻¹ - Real.log ε :=
    inv_sub_log_lt_inv_sub_log hε (hapos k le_rfl)
  have ha0 : 0 < a 0 := hε.trans (hapos 0 (Nat.zero_le k))
  have hu0 : 0 < u 0 := by
    have h := hmono (Nat.zero_le k)
    nlinarith
  have ha0u : a 0 < u 0 / τ := by dsimp only [a]; linarith
  have hlog0 : Real.log (a 0) < Real.log (u 0 / τ) := Real.log_lt_log ha0 ha0u
  have hinv0 : 0 ≤ (a 0)⁻¹ := inv_nonneg.mpr ha0.le
  have hlog : Real.log (u 0 / (ε * τ)) = Real.log (u 0 / τ) - Real.log ε := by
    rw [Real.log_div hu0.ne' (mul_pos hε hτ).ne', Real.log_mul hε.ne' hτ.ne',
      Real.log_div hu0.ne' hτ.ne']
    ring
  have hstrict : φ k - φ 0 < 1 / ε + Real.log (u 0 / (ε * τ)) := by
    rw [hlog, one_div]
    dsimp only [φ] at hφk ⊢
    linarith
  have hlt := (div_lt_iff₀ hr).mp (hsum.trans_lt hstrict)
  have he : (1 / ε + Real.log (u 0 / (ε * τ))) * r =
      r / ε + r * Real.log (u 0 / (ε * τ)) := by ring
  rw [he] at hlt
  exact (not_lt_of_ge hbudget) hlt

end NLAlib
