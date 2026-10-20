import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeGridScale
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Actual source parameter scale and logarithmic grid order

The original variance, covariance and weak parameters imply every budget
used by the fixed-confidence spectral grid. A concrete ceiling order has
both logarithmic size and a checked total failure bound.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- The genuine source parameter inequalities imply all three fixed-grid
budgets at `Δ = sqrt(sigma*v) q^(3/4)`, including its exact fourth power
and positivity whenever the actual weak scale is positive. -/
theorem gaussian_free_delta_budgets {q d : ℕ} (hq : 0 < q) (hd : 0 < d)
    {V W s : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) (_hs : 0 ≤ s)
    (hweak : s ≤ Real.sqrt (Real.sqrt V * Real.sqrt W))
    (hvariance : Real.sqrt V / (d : ℝ) ≤ Real.sqrt W) :
    let σ := Real.sqrt V
    let ξ := Real.sqrt (Real.sqrt V * Real.sqrt W)
    let Δ := ξ * (q : ℝ) ^ (3 / 4 : ℝ)
    s * Real.sqrt (q : ℝ) ≤ Δ ∧ σ / (d : ℝ) ^ 2 ≤ Δ ∧
      (q : ℝ) ^ 3 * (V * W) = Δ ^ 4 ∧ (0 < s → 0 < Δ) := by
  let σ := Real.sqrt V
  let v := Real.sqrt W
  let ξ := Real.sqrt (σ * v)
  let Δ := ξ * (q : ℝ) ^ (3 / 4 : ℝ)
  change s * Real.sqrt (q : ℝ) ≤ Δ ∧ σ / (d : ℝ) ^ 2 ≤ Δ ∧
    (q : ℝ) ^ 3 * (V * W) = Δ ^ 4 ∧ (0 < s → 0 < Δ)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hξ : 0 ≤ ξ := Real.sqrt_nonneg _
  have hqp : 0 < (q : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hqp1 : 1 ≤ (q : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have hξΔ : ξ ≤ Δ := by dsimp [Δ]; nlinarith
  have hqpower : Real.sqrt (q : ℝ) ≤ (q : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hsd0 : 0 ≤ σ / (d : ℝ) := div_nonneg hσ hdp.le
  have hsdσ : σ / (d : ℝ) ≤ σ := div_le_self hσ hd1
  have hsdξ : σ / (d : ℝ) ≤ ξ := by
    apply (sq_le_sq₀ hsd0 hξ).mp
    have hx : ξ ^ 2 = σ * v := Real.sq_sqrt (mul_nonneg hσ hv)
    rw [hx, pow_two]
    exact mul_le_mul hsdσ hvariance hsd0 hσ
  have hxi4 : ξ ^ 4 = V * W := by
    calc
      ξ ^ 4 = (ξ ^ 2) ^ 2 := by ring
      _ = (σ * v) ^ 2 := by rw [Real.sq_sqrt (mul_nonneg hσ hv)]
      _ = V * W := by dsimp [σ, v]; rw [mul_pow, Real.sq_sqrt hV, Real.sq_sqrt hW]
  have hqpow4 : ((q : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = (q : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hweak (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hqpower hξ)
  · calc
      σ / (d : ℝ) ^ 2 = (σ / (d : ℝ)) / (d : ℝ) := by rw [div_div, pow_two]
      _ ≤ σ / (d : ℝ) := div_le_self hsd0 hd1
      _ ≤ ξ := hsdξ
      _ ≤ Δ := hξΔ
  · dsimp [Δ]
    rw [mul_pow, hxi4, hqpow4]
    ring
  · intro hspos
    exact mul_pos (hspos.trans_le hweak) hqp

/-- The concrete natural ceiling order has logarithmic size and leaves
strictly less than one half total localization and grid failure. -/
theorem gaussian_free_logarithmic_order_budgets {d : ℕ} (hd : 2 ≤ d) :
    let q : ℕ := ⌈10 * Real.log (d : ℝ) + 100⌉₊
    0 < q ∧ Real.log (d : ℝ) ≤ q ∧ (q : ℝ) ≤ 212 * Real.log (d : ℝ) ∧
      1 / (16 * (q : ℝ)) + 27 * (d : ℝ) ^ 2 * Real.exp (-(q : ℝ)) ≤ 1 / 2 := by
  let q : ℕ := ⌈10 * Real.log (d : ℝ) + 100⌉₊
  change 0 < q ∧ Real.log (d : ℝ) ≤ q ∧ (q : ℝ) ≤ 212 * Real.log (d : ℝ) ∧ _
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hlog2 : Real.log 2 ≤ Real.log (d : ℝ) := Real.log_le_log (by norm_num) hd2
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (d : ℝ) := by
    nlinarith [Real.log_two_gt_d9]
  have hinput : 0 < 10 * Real.log (d : ℝ) + 100 := by linarith
  have hqpos : 0 < q := Nat.one_le_ceil_iff.mpr hinput
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hqlo : 10 * Real.log (d : ℝ) + 100 ≤ (q : ℝ) := Nat.le_ceil _
  have hqhi : (q : ℝ) < 10 * Real.log (d : ℝ) + 101 := by
    have h := Nat.ceil_lt_add_one hinput.le
    change (q : ℝ) < _ at h
    linarith
  have hsmall : 1 / (16 * (q : ℝ)) ≤ (1 / 16 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hq1])
  have hexp : (d : ℝ) ^ 2 * Real.exp (-(q : ℝ)) ≤ Real.exp (-100) := by
    calc
      _ = Real.exp (2 * Real.log (d : ℝ)) * Real.exp (-(q : ℝ)) := by
        rw [two_mul, Real.exp_add, Real.exp_log hdp, pow_two]
      _ = Real.exp (2 * Real.log (d : ℝ) - (q : ℝ)) := by rw [← Real.exp_add]; congr 1
      _ ≤ Real.exp (-100) := Real.exp_le_exp.mpr (by linarith)
  have hexpsmall : Real.exp (-100) ≤ (1 / 100 : ℝ) := by
    have he100 : (100 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    simpa only [Real.exp_neg, one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) he100)
  refine ⟨hqpos, by linarith, by linarith, ?_⟩
  have hprob := mul_le_mul_of_nonneg_left (hexp.trans hexpsmall) (by norm_num : (0 : ℝ) ≤ 27)
  nlinarith only [hsmall, hprob]

end NLAlib
