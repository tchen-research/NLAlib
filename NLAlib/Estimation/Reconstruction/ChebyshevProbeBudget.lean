import NLAlib.Estimation.Reconstruction.ChebyshevRegression
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Decreasing probe budgets for Chebyshev moment recovery

The prescribed integer budgets are positive and decrease with the degree.
Their total is controlled by a harmonic sum. Coordinate errors of size
`sqrt(j) * gamma` give the weighted moment error required by reconstruction.
Source: Musco--Musco--Rosenblatt--Singh, Section 5, Lemma 18 and Theorem 19.
-/

noncomputable section
open MeasureTheory
namespace NLAlib

/-- The moment accuracy scale for the decreasing-probe spectral estimator. -/
def chebyshevProbeAccuracy (k : ℕ) : ℝ := 1 / (k * Real.sqrt (1 + Real.log k))

/-- The integer number of active probes at a given positive degree. The parameter
`a` is the common numerator `C * log(k / delta)^2 / (n * gamma^2)`. -/
def chebyshevProbeCount (a : ℝ) (j : ℕ) : ℕ := ⌈1 + a / j⌉₊

/-- Every prescribed count is positive, including the totalized degree zero. -/
theorem chebyshevProbeCount_pos {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    0 < chebyshevProbeCount a j := by
  apply Nat.one_le_ceil_iff.mpr
  positivity

/-- Higher positive moments use a shorter prefix of the same probe array. -/
theorem chebyshevProbeCount_antitone {a : ℝ} (ha : 0 ≤ a) :
    AntitoneOn (chebyshevProbeCount a) (Set.Ici 1) := by
  intro i hi j hj hij
  apply Nat.ceil_mono
  change 1 ≤ i at hi
  have hi' : (0 : ℝ) < i := Nat.cast_pos.mpr (by omega)
  simpa only [add_comm] using add_le_add_left
    (div_le_div_of_nonneg_left ha hi' (show (i : ℝ) ≤ j by exact_mod_cast hij)) 1

/-- Reusing the active prefixes requires the sum of the counts, rather than
the degree-weighted sum that would result from restarting each recurrence. -/
theorem sum_chebyshevProbeCount_le {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (∑ j ∈ Finset.Icc 1 k, (chebyshevProbeCount a j : ℝ)) ≤
      2 * k + a * (1 + Real.log k) := by
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 k, (2 + a * (j : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      have := (Nat.ceil_lt_add_one (show 0 ≤ 1 + a / j by positivity)).le
      dsimp [chebyshevProbeCount]
      simpa only [div_eq_mul_inv] using (this.trans_eq (by ring))
    _ = 2 * k + a * (harmonic k : ℝ) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul, ← Finset.mul_sum, harmonic_eq_sum_Icc,
        Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      ring
    _ ≤ _ := by gcongr; exact harmonic_le_one_add_log k

/-- The accuracy scale is strictly positive for positive requested degree. -/
theorem chebyshevProbeAccuracy_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < chebyshevProbeAccuracy k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have := Real.log_nonneg hk'
  unfold chebyshevProbeAccuracy
  positivity

/-- The accuracy normalization cancels the harmonic upper-bound factor exactly. -/
theorem chebyshevProbeAccuracy_sq_mul {k : ℕ} (hk : 1 ≤ k) :
    chebyshevProbeAccuracy k ^ 2 * (1 + Real.log k) = 1 / (k : ℝ) ^ 2 := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < 1 + Real.log k := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast hk)
    linarith
  rw [chebyshevProbeAccuracy, div_pow, mul_pow, Real.sq_sqrt hlog.le]
  field_simp

/-- Each coordinate threshold lies in the quadratic regime of Hanson--Wright. -/
theorem sqrt_mul_chebyshevProbeAccuracy_le_one {k j : ℕ} (hk : 1 ≤ k)
    (hj : j ≤ k) : Real.sqrt j * chebyshevProbeAccuracy k ≤ 1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 1 ≤ 1 + Real.log k := by linarith [Real.log_nonneg hk']
  have hsqrt : 1 ≤ Real.sqrt (1 + Real.log k) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  have hγ : chebyshevProbeAccuracy k ≤ 1 / (k : ℝ) := by
    unfold chebyshevProbeAccuracy
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hj' : Real.sqrt j ≤ (k : ℝ) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    nlinarith
  calc
    _ ≤ (k : ℝ) * (1 / (k : ℝ)) := mul_le_mul hj' hγ
      (chebyshevProbeAccuracy_pos hk).le (by positivity)
    _ = 1 := by field_simp

/-- A universal choice of the source's probe-budget constant, matched to the
proved Hanson--Wright constant `1/(256*exp(1)^2)`. -/
def chebyshevProbeConstant : ℝ := 1024 * Real.exp 1 ^ 2

/-- The numerator common to all decreasing probe budgets. -/
def chebyshevProbeBudget (n k : ℕ) (δ : ℝ) : ℝ :=
  chebyshevProbeConstant * Real.log ((k : ℝ) / δ) ^ 2 /
    (n * chebyshevProbeAccuracy k ^ 2)

/-- The common numerator of the probe counts is nonnegative on total inputs. -/
theorem chebyshevProbeBudget_nonneg (n k : ℕ) (δ : ℝ) :
    0 ≤ chebyshevProbeBudget n k δ := by
  unfold chebyshevProbeBudget chebyshevProbeConstant
  positivity

/-- Explicit query bound for the prescribed counts. -/
theorem sum_chebyshevProbeCount_budget_le {n k : ℕ} (hk : 1 ≤ k) (δ : ℝ) :
    (∑ j ∈ Finset.Icc 1 k, (chebyshevProbeCount (chebyshevProbeBudget n k δ) j : ℝ)) ≤
      2 * k + chebyshevProbeConstant * k ^ 2 * (1 + Real.log k) ^ 2 *
        Real.log ((k : ℝ) / δ) ^ 2 / n := by
  apply (sum_chebyshevProbeCount_le (chebyshevProbeBudget_nonneg n k δ) k).trans_eq
  rw [chebyshevProbeBudget, chebyshevProbeAccuracy, div_pow, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + Real.log k by
      have := Real.log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast hk); linarith)]
  field_simp

/-- The integer budget makes each coordinate failure probability at most
`delta / k`. The parameter range includes every positive dimension. -/
theorem exp_neg_probeCount_mul_le_div {n k j : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    (hj : 0 < j) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    2 * Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
      ((chebyshevProbeCount (chebyshevProbeBudget n k δ) j : ℝ) * n *
        (Real.sqrt j * chebyshevProbeAccuracy k) ^ 2)) ≤ δ / k := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hγ := chebyshevProbeAccuracy_pos (show 1 ≤ k by omega)
  let h := Real.log ((k : ℝ) / δ)
  have hhlog : Real.log 2 ≤ h := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hδ).2 (by nlinarith))
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    linarith
  have hh : 1 / 2 ≤ h := hhalf.trans hhlog
  have hb := Nat.le_ceil (1 + chebyshevProbeBudget n k δ / j)
  have hb' : chebyshevProbeBudget n k δ / j ≤
      (chebyshevProbeCount (chebyshevProbeBudget n k δ) j : ℝ) := by
    dsimp [chebyshevProbeCount]
    linarith
  have hexp : 4 * h ^ 2 ≤ (1 / (256 * Real.exp 1 ^ 2)) *
      ((chebyshevProbeCount (chebyshevProbeBudget n k δ) j : ℝ) * n *
        (Real.sqrt j * chebyshevProbeAccuracy k) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hj'.le]
    have hbmul := mul_le_mul_of_nonneg_right hb'
      (show 0 ≤ (1 / (256 * Real.exp 1 ^ 2)) * n * (j * chebyshevProbeAccuracy k ^ 2) by positivity)
    calc
      _ = chebyshevProbeBudget n k δ / j *
          ((1 / (256 * Real.exp 1 ^ 2)) * n * (j * chebyshevProbeAccuracy k ^ 2)) := by
        dsimp [chebyshevProbeBudget, chebyshevProbeConstant, h]
        field_simp
        ring
      _ ≤ _ := hbmul
      _ = _ := by ring
  calc
    _ ≤ 2 * Real.exp (-(h + Real.log 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = δ / k := by
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
        Real.exp_log (show 0 < (k : ℝ) / δ by positivity), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      field_simp

/-- The coordinate thresholds used in the union bound imply the required
weighted moment error. This is deterministic and requires no independence
between different estimated moments. -/
theorem weightedChebyshevError_le_inv_of_coordinate_error {k : ℕ} (hk : 1 ≤ k)
    (a b : ℕ → ℝ)
    (h : ∀ j ∈ Finset.Icc 1 k,
      |a j - b j| ≤ Real.sqrt j * chebyshevProbeAccuracy k) :
    weightedChebyshevError k a b ≤ 1 / k := by
  have hsum : (∑ j ∈ Finset.Icc 1 k, ((a j - b j) / j) ^ 2) ≤
      chebyshevProbeAccuracy k ^ 2 * (harmonic k : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hj).1; omega)
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
      (chebyshevProbeAccuracy_pos hk).le)).2 (h j hj)
    rw [sq_abs, mul_pow, Real.sq_sqrt hjpos.le] at hs
    simp only [Rat.cast_inv, Rat.cast_natCast, div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hjpos)).2
    calc
      _ ≤ j * chebyshevProbeAccuracy k ^ 2 := hs
      _ = _ := by field_simp
  rw [weightedChebyshevError_eq_sqrt_sum]
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ chebyshevProbeAccuracy k ^ 2 * (harmonic k : ℝ) := hsum
    _ ≤ chebyshevProbeAccuracy k ^ 2 * (1 + Real.log k) := by
      gcongr
      exact harmonic_le_one_add_log k
    _ = (1 / (k : ℝ)) ^ 2 := by rw [chebyshevProbeAccuracy_sq_mul hk, div_pow, one_pow]

end NLAlib
