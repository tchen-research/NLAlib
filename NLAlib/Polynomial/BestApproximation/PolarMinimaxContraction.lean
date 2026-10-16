import NLAlib.Polynomial.BestApproximation.GreedyOddMinimax
import NLAlib.Polynomial.BestApproximation.PolarTaylorCoefficients
/-!+# The sharp scalar contraction of greedy odd minimax updates

The actual minimizer is compared with the proved finite Taylor competitor.
Its attained image endpoints then give the squared-ratio contraction.
Iterating that inequality gives the exponent `(q+1)^T` directly.

Source: Polar Express, Theorems 3.1, 3.3; matrix-toolkit re-derivation §40.
Atlas: `polar-minimax-polynomial-iteration`.
-/
noncomputable section
open Set
namespace NLAlib

/-- Positive interval squared-ratio gaps lie in `[0,1)`. -/
theorem interval_squared_ratio_gap_mem {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 - (a / b) ^ 2 ∈ Ico (0 : ℝ) 1 := by
  have hb : 0 < b := ha.trans_le hab
  have hr : 0 < a / b := div_pos ha hb
  have hr1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  constructor <;> nlinarith

/-- Genuine odd minimax optimality implies the squared-ratio contraction
and a matching bound on the actual uniform error. No recurrence estimate
is assumed in the hypotheses.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem IsOddMinimaxOn.squared_ratio_contraction {q : ℕ} {c : ℕ → ℝ} {a b m M : ℝ}
    (h : IsOddMinimaxOn q c a b) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x ∈ Icc a b, m ≤ oddScalarUpdate q c x ∧ oddScalarUpdate q c x ≤ M)
    (hm : ∃ x ∈ Icc a b, oddScalarUpdate q c x = m)
    (hM : ∃ x ∈ Icc a b, oddScalarUpdate q c x = M) :
    1 - (m / M) ^ 2 ≤ (1 - (a / b) ^ 2) ^ (q + 1) ∧
      oddUniformError q c a b ≤ (1 - (a / b) ^ 2) ^ (q + 1) := by
  let D := (1 - (a / b) ^ 2) ^ (q + 1)
  let r := Real.sqrt (1 - D)
  have hd := interval_squared_ratio_gap_mem ha hab
  have hD0 : 0 ≤ D := pow_nonneg hd.1 _
  have hD1 : D < 1 := pow_lt_one₀ hd.1 hd.2 (by omega)
  have hr : 0 < r := Real.sqrt_pos.mpr (by dsimp only [D]; exact sub_pos.mpr hD1)
  have hrsq : r ^ 2 = 1 - D := Real.sq_sqrt (sub_nonneg.mpr hD1.le)
  have hr1 : r ≤ 1 := by nlinarith [hD0]
  obtain ⟨d, hd⟩ := exists_oddScalarUpdate_interval_competitor q ha hab
  have hscaled : oddUniformError q (fun j => (2 / (r + 1)) * d j) a b ≤ (1 - r) / (r + 1) := by
    apply oddUniformError_le_of_forall (div_nonneg (sub_nonneg.mpr hr1) (by positivity))
    intro x hx
    rw [oddScalarUpdate_smul_coeff]
    exact abs_one_sub_two_div_mul_le hr hr1 (hd x hx)
  have hE : oddUniformError q c a b ≤ (1 - r) / (r + 1) := (h _).trans hscaled
  have hE0 := oddUniformError_nonneg q c a b
  have hEmul : oddUniformError q c a b * (r + 1) ≤ 1 - r :=
    (le_div_iff₀ (by positivity : 0 < r + 1)).mp hE
  obtain ⟨hm0, hmM, hcenter, hEnorm⟩ := h.interval_image_normalized ha hab hbounds hm hM
  have hM0 : 0 < M := hm0.trans_le hmM
  have hrmul : r * M ≤ m := by rw [hEnorm] at hEmul; nlinarith
  have hratio : r ≤ m / M := (le_div_iff₀ hM0).mpr hrmul
  have hsquare : r ^ 2 ≤ (m / M) ^ 2 := pow_le_pow_left₀ hr.le hratio 2
  constructor
  · change 1 - (m / M) ^ 2 ≤ D
    nlinarith
  · change oddUniformError q c a b ≤ D
    have hEr : oddUniformError q c a b ≤ 1 - r := by
      nlinarith [mul_nonneg hE0 hr.le]
    nlinarith

/-- The true squared-ratio gaps of every genuine greedy minimax sequence
obey the iterated power estimate. -/
theorem IsGreedyOddMinimax.squared_ratio_gap_le {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (k : ℕ) :
    1 - (l k / u k) ^ 2 ≤ (1 - ell ^ 2) ^ ((q + 1) ^ k) := by
  induction k with
  | zero => simp [h.lower_zero, h.upper_zero]
  | succ k ih =>
    have hi := h.positive_intervals hell hell1 k
    have hgap := (interval_squared_ratio_gap_mem hi.1 hi.2).1
    have hc := ((h.minimax k).squared_ratio_contraction hi.1 hi.2
      (h.bounds k) (h.attain_lower k) (h.attain_upper k)).1
    calc
      _ ≤ (1 - (l k / u k) ^ 2) ^ (q + 1) := hc
      _ ≤ ((1 - ell ^ 2) ^ ((q + 1) ^ k)) ^ (q + 1) := pow_le_pow_left₀ hgap ih _
      _ = (1 - ell ^ 2) ^ ((q + 1) ^ (k + 1)) := by rw [← pow_mul, Nat.pow_succ]

/-- The actual per-step uniform error has the final iterated power rate. -/
theorem IsGreedyOddMinimax.uniform_error_le {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (k : ℕ) :
    oddUniformError q (c k) (l k) (u k) ≤ (1 - ell ^ 2) ^ ((q + 1) ^ (k + 1)) := by
  have hi := h.positive_intervals hell hell1 k
  have hgap := (interval_squared_ratio_gap_mem hi.1 hi.2).1
  calc
    _ ≤ (1 - (l k / u k) ^ 2) ^ (q + 1) :=
      ((h.minimax k).squared_ratio_contraction hi.1 hi.2
        (h.bounds k) (h.attain_lower k) (h.attain_upper k)).2
    _ ≤ ((1 - ell ^ 2) ^ ((q + 1) ^ k)) ^ (q + 1) :=
      pow_le_pow_left₀ hgap (h.squared_ratio_gap_le hell hell1 k) _
    _ = (1 - ell ^ 2) ^ ((q + 1) ^ (k + 1)) := by rw [← pow_mul, Nat.pow_succ]

/-- Every genuine greedy odd minimax scalar composition has the sharp
polar iteration rate, via its actual next lower interval endpoint.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem IsGreedyOddMinimax.composition_error_le {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) {T : ℕ} (hT : 1 ≤ T)
    {x : ℝ} (hx : x ∈ Icc ell 1) :
    |1 - oddScalarComposition q c x T| ≤ 1 - l T ∧
      1 - l T ≤ (1 - ell ^ 2) ^ ((q + 1) ^ T) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  have he := abs_one_sub_oddScalarUpdate_le q (c k) (l k) (u k)
    (oddScalarComposition q c x k) (h.composition_mem_interval hx k)
  have hnorm := (h.normalized_images hell hell1 k).2
  rw [hnorm] at he
  exact ⟨he, hnorm ▸ h.uniform_error_le hell hell1 k⟩

end NLAlib
